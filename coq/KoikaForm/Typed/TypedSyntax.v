(*! Language | Typed ASTs !*)
Require Export Koika.Utils.Common.
Require Export Koika.Utils.Environments.
Require Export Koika.KoikaForm.Types.
Require Export Koika.Primitives.
Import PrimTyped PrimSignatures.

Section Syntax.
  Context {pos_t var_t rule_name_t fn_name_t reg_t ext_fn_t: Type}.
  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  Inductive action: tsig var_t -> type -> Type :=
  | Fail {sig} tau: action sig tau
  | Var {sig} {k: var_t} {tau: type} (m: member (k, tau) sig): action sig tau
  | Const {sig} {tau: type} (cst: type_denote tau): action sig tau
  | Assign {sig} {k: var_t} {tau: type} (m: member (k, tau) sig)
    (ex: action sig tau): action sig unit_t
  | Seq {sig tau} (r1: action sig unit_t) (r2: action sig tau): action sig tau
  | Bind {sig} {tau tau'} (var: var_t) (ex: action sig tau)
    (body: action (List.cons (var, tau) sig) tau'): action sig tau'
  | If {sig tau} (cond: action sig (bits_t 1)) (tbranch fbranch: action sig tau)
    : action sig tau
  | Read {sig} (port: Port) (idx: reg_t): action sig (R idx)
  | Write {sig} (port: Port) (idx: reg_t) (value: action sig (R idx))
    : action sig unit_t
  | Unop {sig} (fn: fn1) (arg1: action sig (Sigma1 fn).(arg1Sig))
    : action sig (Sigma1 fn).(retSig)
  | Binop {sig} (fn: fn2) (arg1: action sig (Sigma2 fn).(arg1Sig))
    (arg2: action sig (Sigma2 fn).(arg2Sig)): action sig (Sigma2 fn).(retSig)
  | ExternalCall {sig} (fn: ext_fn_t) (arg: action sig (Sigma fn).(arg1Sig))
    : action sig (Sigma fn).(retSig)
  | InternalCall {sig tau} (fn : fn_name_t) {argspec : tsig var_t}
    (args: context (fun k_tau => action sig (snd k_tau)) (List.rev argspec))
    (body : action (List.rev argspec) tau): action sig tau
  | APos {sig tau} (pos: pos_t) (a: action sig tau): action sig tau.

  Definition rule := action nil unit_t.
End Syntax.

Arguments action pos_t var_t fn_name_t {reg_t ext_fn_t} R Sigma sig tau: assert.
Arguments rule pos_t var_t fn_name_t {reg_t ext_fn_t} R Sigma: assert.
