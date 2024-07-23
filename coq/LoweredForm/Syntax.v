(*! Language | Lowered ASTs (weakly-typed) !*)
Require Export Koika.Utils.Common.
Require Export Koika.Utils.Environments.
Require Export Koika.KoikaForm.Types.
Require Export Koika.Primitives.
Import PrimTyped CircuitSignatures.

Section Syntax.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.
  Context {R: reg_t -> nat}.
  Context {Sigma: ext_fn_t -> CExternalSignature}.

  Inductive action : lsig -> nat -> Type :=
  | Fail {sig} sz : action sig sz
  | Var {sig} (k: var_t) {sz: nat} (m: member sz sig) : action sig sz
  | Const {sig} {sz: nat} (cst: bits sz) : action sig sz
  | Assign {sig} (k: var_t) {sz: nat} (m: member sz sig) (ex: action sig sz)
    : action sig 0
  | Seq {sig sz} (r1: action sig 0) (r2: action sig sz) : action sig sz
  | Bind {sig} (k: var_t) {sz sz'} (ex: action sig sz)
         (body: action (List.cons sz sig) sz') : action sig sz'
  | If {sig sz} (cond: action sig 1)
       (tbranch fbranch: action sig sz) : action sig sz
  | Read {sig} (port: Port) (idx: reg_t): action sig (R idx)
  | Write {sig} (port: Port) (idx: reg_t)
          (value: action sig (R idx)) : action sig 0
  | Unop {sig} (fn: fbits1) (arg1: action sig (arg1Sig (CSigma1 fn)))
    : action sig (CSigma1 fn).(retSig)
  | Binop {sig} (fn: fbits2) (arg1: action sig (arg1Sig (CSigma2 fn)))
          (arg2: action sig (arg2Sig (CSigma2 fn)))
    : action sig (CSigma2 fn).(retSig)
  | ExternalCall {sig} (fn: ext_fn_t) (arg: action sig (arg1Sig (Sigma fn)))
    : action sig (Sigma fn).(retSig)
  | APos {sig sz} (pos: pos_t) (a: action sig sz) : action sig sz.

  Definition rule := action nil 0.
End Syntax.

Arguments rule pos_t var_t {reg_t ext_fn_t} R Sigma : assert.
Arguments action pos_t var_t {reg_t ext_fn_t} R Sigma sig sz : assert.
