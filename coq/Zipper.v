(*! Proving | Zippers for uactions as well as functions for searching the
   syntactic tree !*)

Require Import List.
Require Import Koika.Syntax.
Open Scope nat.

Inductive zipper := here | through_nth_branch (n: nat) (b: zipper).

Definition zoom_zipper
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t) (bc: zipper)
: option (uaction pos_t var_t fn_name_t reg_t ext_fn_t * zipper) :=
  match bc with
  | here => None
  | through_nth_branch n sbc =>
    match ua with
    | UAssign v a => if n =? 0 then Some (a, sbc) else None
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
    | Some (ua', bc') => zoom_n_zipper ua' n' bc'
    | None => None
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
    match zoom_zipper ua bc with
    | Some (ua', _) => access_zipper ua' sbc
    | None => None
    end
  end.

Fixpoint find_all_in_uaction
  {pos_t var_t fn_name_t reg_t ext_fn_t: Type}
  (ua: uaction pos_t var_t fn_name_t reg_t ext_fn_t)
  (pred: uaction pos_t var_t fn_name_t reg_t ext_fn_t -> bool)
: list zipper :=
  app
    (if pred ua then [here] else [])
    (match ua with
    | UAssign _ ex =>
      map (fun bc => through_nth_branch 0 bc) (find_all_in_uaction ex pred)
    | USeq a1 a2 =>
      app
        (map (fun bc => through_nth_branch 0 bc) (find_all_in_uaction a1 pred))
        (map (fun bc => through_nth_branch 1 bc) (find_all_in_uaction a2 pred))
    | UBind _ ex b =>
      app
        (map (fun bc => through_nth_branch 0 bc) (find_all_in_uaction ex pred))
        (map (fun bc => through_nth_branch 1 bc) (find_all_in_uaction b pred))
    | UIf c t f =>
      app
        (app
          (map (fun bc => through_nth_branch 0 bc) (find_all_in_uaction c pred))
          (map (fun bc => through_nth_branch 1 bc) (find_all_in_uaction t pred))
        )
        (map (fun bc => through_nth_branch 2 bc) (find_all_in_uaction f pred))
    | UWrite _ _ a =>
      map (fun bc => through_nth_branch 0 bc) (find_all_in_uaction a pred)
    | UUnop _ a =>
      map (fun bc => through_nth_branch 0 bc) (find_all_in_uaction a pred)
    | UBinop _ a1 a2 =>
      app
        (map (fun bc => through_nth_branch 0 bc) (find_all_in_uaction a1 pred))
        (map (fun bc => through_nth_branch 1 bc) (find_all_in_uaction a2 pred))
    | UExternalCall _ a =>
      map (fun bc => through_nth_branch 0 bc) (find_all_in_uaction a pred)
    | UInternalCall ufn al =>
      app
        (map
          (fun bc => through_nth_branch 0 bc)
          (find_all_in_uaction (int_body ufn) pred)
        )
        (List.concat (snd (fold_left
          (fun acc ua => (
            S (fst acc), (find_all_in_uaction ua pred) :: (snd acc))
          )
          al (1, [])
        )))
    | UAPos _ e =>
      map (fun bc => through_nth_branch 0 bc) (find_all_in_uaction e pred)
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
Close Scope nat.
