
type __ = Obj.t

val pred : int -> int

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val pow : int -> int -> int
 end

module Pos :
 sig
  val succ : int -> int

  val of_succ_nat : int -> int
 end

module N :
 sig
  val of_nat : int -> int
 end

type index = int

type ('a, 'b) vect_cons_t = { vhd : 'a; vtl : 'b }

type 't vect = __

val vect_cons : int -> 'a1 -> 'a1 vect -> ('a1, __) vect_cons_t

val vect_const : int -> 'a1 -> 'a1 vect

val pow2 : int -> int

module Bits :
 sig
  val of_positive : int -> int -> bool vect

  val of_N : int -> int -> bool vect

  val of_nat : int -> int -> bool vect
 end

type 't finiteType = { finite_index : ('t -> int); finite_elements : 't list }

type 'a show = { show0 : ('a -> char list) }

val show_string : char list show

type 'k member =
| MemberHd of 'k * 'k list
| MemberTl of 'k * 'k * 'k list * 'k member

val nth_member : 'a1 list -> int -> 'a1 -> 'a1 member

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

val chd : 'a1 -> 'a1 list -> ('a1, 'a2) context -> 'a2

val ctl : 'a1 -> 'a1 list -> ('a1, 'a2) context -> ('a1, 'a2) context

val ccreate : 'a1 list -> ('a1 -> 'a1 member -> 'a2) -> ('a1, 'a2) context

val cassoc : 'a1 list -> 'a1 -> 'a1 member -> ('a1, 'a2) context -> 'a2

val creplace :
  'a1 list -> 'a1 -> 'a1 member -> 'a2 -> ('a1, 'a2) context -> ('a1, 'a2)
  context

type 'k env = { getenv : (__ -> __ -> 'k -> __);
                putenv : (__ -> __ -> 'k -> __ -> __);
                create : (__ -> ('k -> __) -> __); finite_keys : 'k finiteType }

type ('k, 'v) env_t = __

val getenv : 'a1 env -> ('a1, 'a2) env_t -> 'a1 -> 'a2

val finite_member : 'a1 finiteType -> 'a1 -> 'a1 member

val contextEnv : 'a1 finiteType -> 'a1 env

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

module PrimTyped :
 sig
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

module Backends :
 sig
  val register : interop_package_t -> unit
 end

type pos_t = unit

type var_t = char list

type fn_name_t = char list

val sz : int

type reg_t =
| Input_buffer
| Queue_empty
| Queue_data
| Output_buffer

val r : reg_t -> type0

type ext_fn_t =
| NextInput
| F
| G

val sigma : ext_fn_t -> externalSignature

type rule_name_t =
| DoF
| DoG

val rules : rule_name_t -> (pos_t, var_t, fn_name_t, reg_t, ext_fn_t) rule

val pipeline : (pos_t, rule_name_t) scheduler

val finiteType_reg_t : reg_t finiteType

val r0 : (reg_t, type_denote) env_t

val external0 : rule_name_t -> bool

val cpp_extfuns : char list

val ext_fn_names : ext_fn_t -> char list

val package : interop_package_t

val prog : unit
