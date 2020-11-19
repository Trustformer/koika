
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val pred : int -> int **)

let pred = fun n -> Pervasives.max 0 (n-1)

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Pervasives.succ (add p m))
      n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Pervasives.succ 0)
      (fun m0 -> mul n (pow n m0))
      m
 end

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Pervasives.succ

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n
 end

module N =
 struct
  (** val of_nat : int -> int **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' -> (Pos.of_succ_nat n'))
      n
 end

type index = int

type ('a, 'b) vect_cons_t = { vhd : 'a; vtl : 'b }

type 't vect = __

(** val vect_cons : int -> 'a1 -> 'a1 vect -> ('a1, __) vect_cons_t **)

let vect_cons _ t v =
  { vhd = t; vtl = v }

(** val vect_const : int -> 'a1 -> 'a1 vect **)

let rec vect_const sz0 t =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic __)
    (fun sz1 -> Obj.magic vect_cons sz1 t (vect_const sz1 t))
    sz0

(** val pow2 : int -> int **)

let pow2 n =
  Pervasives.succ (pred (Nat.pow (Pervasives.succ (Pervasives.succ 0)) n))

module Bits =
 struct
  (** val of_positive : int -> int -> bool vect **)

  let rec of_positive sz0 p =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Obj.magic __)
      (fun sz1 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 ->
        Obj.magic vect_cons sz1 true (of_positive sz1 p0))
        (fun p0 ->
        Obj.magic vect_cons sz1 false (of_positive sz1 p0))
        (fun _ -> Obj.magic vect_cons sz1 true (vect_const sz1 false))
        p)
      sz0

  (** val of_N : int -> int -> bool vect **)

  let of_N sz0 n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> vect_const sz0 false)
      (fun p -> of_positive sz0 p)
      n

  (** val of_nat : int -> int -> bool vect **)

  let of_nat sz0 n =
    of_N sz0 (N.of_nat n)
 end

type 't finiteType = { finite_index : ('t -> int); finite_elements : 't list }

type 'a show = { show0 : ('a -> char list) }

(** val show_string : char list show **)

let show_string =
  { show0 = (fun x -> x) }

type 'k member =
| MemberHd of 'k * 'k list
| MemberTl of 'k * 'k * 'k list * 'k member

(** val nth_member : 'a1 list -> int -> 'a1 -> 'a1 member **)

let nth_member ls idx t =
  let rec f l idx0 =
    match l with
    | [] ->
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ _ _ -> assert false (* absurd case *))
         (fun _ _ _ -> assert false (* absurd case *))
         idx0)
    | y :: l0 ->
      (fun t0 _ ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> MemberHd (t0, l0))
          (fun idx1 -> MemberTl (t0, y, l0, (f l0 idx1 t0 __)))
          idx0)
  in f ls idx t __

type 'a struct_sig' = { struct_name : char list;
                        struct_fields : (char list * 'a) list }

type enum_sig = { enum_name : char list; enum_size : int; enum_bitsize : 
                  int; enum_members : char list vect;
                  enum_bitpatterns : bool vect vect }

type 'a array_sig' = { array_type : 'a; array_len : int }

type type0 =
| Bits_t of int
| Enum_t of enum_sig
| Struct_t of type0 struct_sig'
| Array_t of type0 array_sig'

type struct_index = index

type array_index = index

type port =
| P0
| P1

type type_denote = __

type 'argKind _Sig = { argSigs : 'argKind vect; retSig : 'argKind }

type externalSignature = type0 _Sig

type 'var_t tsig = ('var_t * type0) list

type ('k, 'v) context =
| CtxEmpty
| CtxCons of 'k list * 'k * 'v * ('k, 'v) context

(** val chd : 'a1 -> 'a1 list -> ('a1, 'a2) context -> 'a2 **)

let chd _ _ = function
| CtxEmpty -> Obj.magic ()
| CtxCons (_, _, v, _) -> v

(** val ctl : 'a1 -> 'a1 list -> ('a1, 'a2) context -> ('a1, 'a2) context **)

let ctl _ _ = function
| CtxEmpty -> Obj.magic ()
| CtxCons (_, _, _, ctx') -> ctx'

(** val ccreate :
    'a1 list -> ('a1 -> 'a1 member -> 'a2) -> ('a1, 'a2) context **)

let rec ccreate sig0 f =
  match sig0 with
  | [] -> CtxEmpty
  | h :: t ->
    CtxCons (t, h, (f h (MemberHd (h, t))),
      (ccreate t (fun k m -> f k (MemberTl (k, h, t, m)))))

(** val cassoc :
    'a1 list -> 'a1 -> 'a1 member -> ('a1, 'a2) context -> 'a2 **)

let rec cassoc _ _ m ctx =
  match m with
  | MemberHd (k, sig0) -> chd k sig0 ctx
  | MemberTl (k, k', sig0, m0) -> cassoc sig0 k m0 (ctl k' sig0 ctx)

(** val creplace :
    'a1 list -> 'a1 -> 'a1 member -> 'a2 -> ('a1, 'a2) context -> ('a1, 'a2)
    context **)

let rec creplace _ _ m v ctx =
  match m with
  | MemberHd (k, sig0) -> CtxCons (sig0, k, v, (ctl k sig0 ctx))
  | MemberTl (k, k', sig0, m0) ->
    CtxCons (sig0, k', (chd k' sig0 ctx),
      (creplace sig0 k m0 v (ctl k' sig0 ctx)))

type 'k env = { getenv : (__ -> __ -> 'k -> __);
                putenv : (__ -> __ -> 'k -> __ -> __);
                create : (__ -> ('k -> __) -> __); finite_keys : 'k finiteType }

type ('k, 'v) env_t = __

(** val getenv : 'a1 env -> ('a1, 'a2) env_t -> 'a1 -> 'a2 **)

let getenv e x k =
  Obj.magic e.getenv __ x k

(** val finite_member : 'a1 finiteType -> 'a1 -> 'a1 member **)

let finite_member fT t =
  nth_member fT.finite_elements (fT.finite_index t) t

(** val contextEnv : 'a1 finiteType -> 'a1 env **)

let contextEnv fT =
  { getenv = (fun _ ctx k ->
    cassoc fT.finite_elements k (finite_member fT k) (Obj.magic ctx));
    putenv = (fun _ ctx k v ->
    Obj.magic creplace fT.finite_elements k (finite_member fT k) v ctx);
    create = (fun _ fn ->
    Obj.magic ccreate fT.finite_elements (fun k _ -> fn k)); finite_keys =
    fT }

type bits_comparison =
| CLt
| CGt
| CLe
| CGe

type bits_display_style =
| DBin
| DDec
| DHex
| DFull

type display_options = { display_strings : bool; display_newline : bool;
                         display_style : bits_display_style }

module PrimTyped =
 struct
  type fdisplay =
  | DisplayUtf8 of int
  | DisplayValue of type0 * display_options

  type fconv =
  | Pack
  | Unpack
  | Ignore

  type lowered1 =
  | IgnoreBits of int
  | DisplayBits of fdisplay

  type fbits1 =
  | Not of int
  | SExt of int * int
  | ZExtL of int * int
  | ZExtR of int * int
  | Repeat of int * int
  | Slice of int * int * int
  | Lowered of lowered1

  type fbits2 =
  | And of int
  | Or of int
  | Xor of int
  | Lsl of int * int
  | Lsr of int * int
  | Asr of int * int
  | Concat of int * int
  | Sel of int
  | SliceSubst of int * int * int
  | IndexedSlice of int * int
  | Plus of int
  | Minus of int
  | Mul of int * int
  | EqBits of int * bool
  | Compare of bool * bits_comparison * int

  type fn1 =
  | Display of fdisplay
  | Conv of type0 * fconv
  | Bits1 of fbits1
  | Struct1 of type0 struct_sig' * struct_index
  | Array1 of type0 array_sig' * array_index

  type fn2 =
  | Eq of type0 * bool
  | Bits2 of fbits2
  | Struct2 of type0 struct_sig' * struct_index
  | Array2 of type0 array_sig' * array_index
 end

type ('pos_t, 'rule_name_t) scheduler =
| Done
| Cons of 'rule_name_t * ('pos_t, 'rule_name_t) scheduler
| Try of 'rule_name_t * ('pos_t, 'rule_name_t) scheduler
   * ('pos_t, 'rule_name_t) scheduler
| SPos of 'pos_t * ('pos_t, 'rule_name_t) scheduler

type ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action =
| Fail of 'var_t tsig * type0
| Var of ('var_t * type0) list * 'var_t * type0 * ('var_t * type0) member
| Const of 'var_t tsig * type0 * type_denote
| Assign of ('var_t * type0) list * 'var_t * type0 * ('var_t * type0) member
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
| Seq of 'var_t tsig * type0
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
| Bind of 'var_t tsig * type0 * type0 * 'var_t
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
| If of 'var_t tsig * type0
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
| Read of 'var_t tsig * port * 'reg_t
| Write of 'var_t tsig * port * 'reg_t
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
| Unop of 'var_t tsig * PrimTyped.fn1
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
| Binop of 'var_t tsig * PrimTyped.fn2
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
| ExternalCall of 'var_t tsig * 'ext_fn_t
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
| InternalCall of 'var_t tsig * type0 * 'fn_name_t * 'var_t tsig
   * ('var_t * type0, ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action)
     context * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
| APos of 'var_t tsig * type0 * 'pos_t
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action

type ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) rule =
  ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action

type ext_fn_rtl_spec = { efr_name : char list; efr_internal : bool }

type ext_fn_sim_spec = { efs_name : char list; efs_method : bool }

type ('pos_t, 'var_t, 'fn_name_t, 'rule_name_t, 'reg_t, 'ext_fn_t) koika_package_t = { 
koika_var_names : 'var_t show; koika_fn_names : 'fn_name_t show;
koika_reg_names : 'reg_t show; koika_reg_types : ('reg_t -> type0);
koika_reg_init : ('reg_t -> type_denote);
koika_reg_finite : 'reg_t finiteType;
koika_ext_fn_types : ('ext_fn_t -> externalSignature);
koika_rules : ('rule_name_t -> ('pos_t, 'var_t, 'fn_name_t, 'reg_t,
              'ext_fn_t) rule); koika_rule_external : ('rule_name_t -> bool);
koika_rule_names : 'rule_name_t show;
koika_scheduler : ('pos_t, 'rule_name_t) scheduler;
koika_module_name : char list }

type 'ext_fn_t verilog_package_t = { vp_ext_fn_specs : ('ext_fn_t ->
                                                       ext_fn_rtl_spec) }

type 'ext_fn_t sim_package_t = { sp_ext_fn_specs : ('ext_fn_t ->
                                                   ext_fn_sim_spec);
                                 sp_prelude : char list option }

type interop_package_t = { ip_koika : (unit, char list, char list, __, __,
                                      __) koika_package_t;
                           ip_verilog : __ verilog_package_t;
                           ip_sim : __ sim_package_t }

module Backends =
 struct
  (** val register : interop_package_t -> unit **)

  let register = fun ip -> Registry.register (Obj.magic ip)
 end

type pos_t = unit

type var_t = char list

type fn_name_t = char list

(** val sz : int **)

let sz =
  pow2 (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))

type reg_t =
| Input_buffer
| Queue_empty
| Queue_data
| Output_buffer

(** val r : reg_t -> type0 **)

let r = function
| Queue_empty -> Bits_t (Pervasives.succ 0)
| _ -> Bits_t sz

type ext_fn_t =
| NextInput
| F
| G

(** val sigma : ext_fn_t -> externalSignature **)

let sigma _ =
  { argSigs = (Obj.magic vect_cons 0 (Bits_t sz) __); retSig = (Bits_t sz) }

type rule_name_t =
| DoF
| DoG

(** val rules :
    rule_name_t -> (pos_t, var_t, fn_name_t, reg_t, ext_fn_t) rule **)

let rules = function
| DoF ->
  Bind ([], (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))))))))))))))))))))), (Bits_t 0),
    ('v'::[]), (Read ([], P0, Input_buffer)), (Seq (((('v'::[]), (Bits_t
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: []), (Bits_t 0), (Write
    (((('v'::[]), (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))))))))))))))))))))) :: []), P0,
    Input_buffer, (ExternalCall (((('v'::[]), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: []), NextInput, (Var (((('v'::[]),
    (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))))))))))))))))))))) :: []), ('v'::[]),
    (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))))))))))))))))))))), (MemberHd
    ((('v'::[]), (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))))))))))))))))))))), [])))))))), (Bind
    (((('v'::[]), (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))))))))))))))))))))) :: []), (Bits_t
    (Pervasives.succ 0)), (Bits_t 0),
    ('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Read (((('v'::[]), (Bits_t (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: []), P1, Queue_empty)), (If
    (((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: ((('v'::[]), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: [])), (Bits_t 0), (Var
    (((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: ((('v'::[]), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: [])),
    ('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0)), (MemberHd
    ((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))), ((('v'::[]), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: []))))), (Seq
    (((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: ((('v'::[]), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: [])), (Bits_t 0), (Write
    (((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: ((('v'::[]), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: [])), P1, Queue_empty, (Const
    (((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: ((('v'::[]), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: [])), (Bits_t (Pervasives.succ
    0)), (Obj.magic { vhd = false; vtl = __ }))))), (Write
    (((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: ((('v'::[]), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: [])), P0, Queue_data,
    (ExternalCall
    (((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: ((('v'::[]), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: [])), F, (Var
    (((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: ((('v'::[]), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: [])), ('v'::[]), (Bits_t
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))))))))))))))))))))))), (MemberTl ((('v'::[]), (Bits_t
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))),
    (('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))), ((('v'::[]), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: []), (MemberHd ((('v'::[]),
    (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))))))))))))))))))))), [])))))))))))),
    (Fail
    (((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: ((('v'::[]), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: [])), (Bits_t 0))))))))))
| DoG ->
  Bind ([], (Bits_t (Pervasives.succ 0)), (Bits_t 0),
    ('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Read ([], P0, Queue_empty)), (If
    (((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: []), (Bits_t 0), (Unop
    (((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: []), (PrimTyped.Bits1 (PrimTyped.Not
    (Pervasives.succ 0))), (Var
    (((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: []),
    ('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0)), (MemberHd
    ((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))), [])))))), (Bind
    (((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: []), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))))))))))))))))))))))), (Bits_t 0),
    ('d'::('a'::('t'::('a'::[])))), (Read
    (((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: []), P0, Queue_data)), (Seq
    (((('d'::('a'::('t'::('a'::[])))), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: ((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: [])), (Bits_t 0), (Write
    (((('d'::('a'::('t'::('a'::[])))), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: ((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: [])), P0, Output_buffer, (ExternalCall
    (((('d'::('a'::('t'::('a'::[])))), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: ((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: [])), G, (Var
    (((('d'::('a'::('t'::('a'::[])))), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: ((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: [])), ('d'::('a'::('t'::('a'::[])))),
    (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))))))))))))))))))))), (MemberHd
    ((('d'::('a'::('t'::('a'::[])))), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))),
    ((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: []))))))))), (Write
    (((('d'::('a'::('t'::('a'::[])))), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: ((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: [])), P0, Queue_empty, (Const
    (((('d'::('a'::('t'::('a'::[])))), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: ((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: [])), (Bits_t (Pervasives.succ 0)),
    (Obj.magic { vhd = true; vtl = __ }))))))))), (Fail
    (((('q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))),
    (Bits_t (Pervasives.succ 0))) :: []), (Bits_t 0))))))

(** val pipeline : (pos_t, rule_name_t) scheduler **)

let pipeline =
  Cons (DoG, (Cons (DoF, Done)))

(** val finiteType_reg_t : reg_t finiteType **)

let finiteType_reg_t =
  { finite_index = (fun h ->
    match h with
    | Input_buffer -> 0
    | Queue_empty -> Pervasives.succ 0
    | Queue_data -> Pervasives.succ (Pervasives.succ 0)
    | Output_buffer -> Pervasives.succ (Pervasives.succ (Pervasives.succ 0)));
    finite_elements =
    (Input_buffer :: (Queue_empty :: (Queue_data :: (Output_buffer :: [])))) }

(** val r0 : (reg_t, type_denote) env_t **)

let r0 =
  Obj.magic (CtxCons ((Queue_empty :: (Queue_data :: (Output_buffer :: []))),
    Input_buffer,
    (Bits.of_nat (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))))))))))))))))))))))))))))))) (Pervasives.succ 0)),
    (CtxCons ((Queue_data :: (Output_buffer :: [])), Queue_empty,
    (Obj.magic vect_cons 0 true __), (CtxCons ((Output_buffer :: []),
    Queue_data,
    (Bits.of_nat (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))))))))))))))))))))))))))))))) 0), (CtxCons ([],
    Output_buffer,
    (Bits.of_nat (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))))))))))))))))))))))))))))))) 0), CtxEmpty))))))))

(** val external0 : rule_name_t -> bool **)

let external0 _ =
  false

(** val cpp_extfuns : char list **)

let cpp_extfuns =
  'c'::('l'::('a'::('s'::('s'::(' '::('e'::('x'::('t'::('f'::('u'::('n'::('s'::(' '::('{'::('\n'::('p'::('u'::('b'::('l'::('i'::('c'::(':'::('\n'::(' '::(' '::('s'::('t'::('a'::('t'::('i'::('c'::(' '::('b'::('i'::('t'::('s'::('<'::('3'::('2'::('>'::(' '::('n'::('e'::('x'::('t'::('_'::('i'::('n'::('p'::('u'::('t'::('('::('b'::('i'::('t'::('s'::('<'::('3'::('2'::('>'::(' '::('s'::('t'::(')'::(' '::('{'::('\n'::(' '::(' '::(' '::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('s'::('t'::(' '::('+'::(' '::('b'::('i'::('t'::('s'::('<'::('3'::('2'::('>'::('{'::('2'::('}'::(';'::('\n'::(' '::(' '::('}'::('\n'::('\n'::(' '::(' '::('s'::('t'::('a'::('t'::('i'::('c'::(' '::('b'::('i'::('t'::('s'::('<'::('3'::('2'::('>'::(' '::('f'::('('::('b'::('i'::('t'::('s'::('<'::('3'::('2'::('>'::(' '::('x'::(')'::(' '::('{'::('\n'::(' '::(' '::(' '::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('p'::('r'::('i'::('m'::('s'::(':'::(':'::('s'::('l'::('i'::('c'::('e'::('<'::('0'::(','::(' '::('3'::('2'::('>'::('('::('x'::(' '::('*'::(' '::('b'::('i'::('t'::('s'::('<'::('3'::('2'::('>'::('{'::('5'::('}'::(')'::(';'::('\n'::(' '::(' '::('}'::('\n'::('\n'::(' '::(' '::('s'::('t'::('a'::('t'::('i'::('c'::(' '::('b'::('i'::('t'::('s'::('<'::('3'::('2'::('>'::(' '::('g'::('('::('b'::('i'::('t'::('s'::('<'::('3'::('2'::('>'::(' '::('x'::(')'::(' '::('{'::('\n'::(' '::(' '::(' '::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('x'::(' '::('+'::(' '::('b'::('i'::('t'::('s'::('<'::('3'::('2'::('>'::('{'::('1'::('}'::(';'::('\n'::(' '::(' '::('}'::('\n'::('}'::(';'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val ext_fn_names : ext_fn_t -> char list **)

let ext_fn_names = function
| NextInput ->
  'n'::('e'::('x'::('t'::('_'::('i'::('n'::('p'::('u'::('t'::[])))))))))
| F -> 'f'::[]
| G -> 'g'::[]

(** val package : interop_package_t **)

let package =
  { ip_koika = { koika_var_names = show_string; koika_fn_names = show_string;
    koika_reg_names = { show0 = (fun h ->
    match Obj.magic h with
    | Input_buffer ->
      'i'::('n'::('p'::('u'::('t'::('_'::('b'::('u'::('f'::('f'::('e'::('r'::[])))))))))))
    | Queue_empty ->
      'q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))
    | Queue_data ->
      'q'::('u'::('e'::('u'::('e'::('_'::('d'::('a'::('t'::('a'::[])))))))))
    | Output_buffer ->
      'o'::('u'::('t'::('p'::('u'::('t'::('_'::('b'::('u'::('f'::('f'::('e'::('r'::[]))))))))))))) };
    koika_reg_types = (Obj.magic r); koika_reg_init = (fun reg ->
    getenv (contextEnv (Obj.magic finiteType_reg_t)) r0 reg);
    koika_reg_finite = (Obj.magic finiteType_reg_t); koika_ext_fn_types =
    (Obj.magic sigma); koika_rules = (Obj.magic rules); koika_rule_external =
    (Obj.magic external0); koika_rule_names = { show0 = (fun h ->
    match Obj.magic h with
    | DoF -> 'd'::('o'::('F'::[]))
    | DoG -> 'd'::('o'::('G'::[]))) }; koika_scheduler =
    (Obj.magic pipeline); koika_module_name =
    ('p'::('i'::('p'::('e'::('l'::('i'::('n'::('e'::('_'::('t'::('u'::('t'::('o'::('r'::('i'::('a'::('l'::[]))))))))))))))))) };
    ip_verilog = { vp_ext_fn_specs = (fun fn -> { efr_name =
    (ext_fn_names (Obj.magic fn)); efr_internal =
    (match Obj.magic fn with
     | NextInput -> false
     | _ -> true) }) }; ip_sim = { sp_ext_fn_specs = (fun fn -> { efs_name =
    (ext_fn_names (Obj.magic fn)); efs_method = false }); sp_prelude = (Some
    cpp_extfuns) } }

(** val prog : unit **)

let prog =
  Backends.register package
