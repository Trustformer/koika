
type __ = Obj.t

val negb : bool -> bool

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val id : 'a1 -> 'a1

type 'a sig0 =
| Exist of 'a

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

val projT2 : ('a1, 'a2) sigT -> 'a2



val pred : int -> int

val add : int -> int -> int

val mul : int -> int -> int

val sub : int -> int -> int

module Nat :
 sig
  val pred : int -> int

  val add : int -> int -> int

  val mul : int -> int -> int

  val sub : int -> int -> int

  val compare : int -> int -> comparison

  val max : int -> int -> int

  val pow : int -> int -> int

  val divmod : int -> int -> int -> int -> int * int

  val div : int -> int -> int

  val modulo : int -> int -> int

  val log2_iter : int -> int -> int -> int -> int

  val log2 : int -> int

  val log2_up : int -> int
 end

val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val find : ('a1 -> bool) -> 'a1 list -> 'a1 option

val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list

val skipn : int -> 'a1 list -> 'a1 list

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val mul : int -> int -> int

  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> int

  val of_succ_nat : int -> int
 end

module N :
 sig
  val zero : int

  val add : int -> int -> int

  val mul : int -> int -> int

  val to_nat : int -> int

  val of_nat : int -> int
 end

val le_gt_dec : int -> int -> bool



val append : char list -> char list -> char list

val length0 : char list -> int

type 't eqDec = { eq_dec : ('t -> 't -> bool) }

val beq_dec : 'a1 eqDec -> 'a1 -> 'a1 -> bool

val eqDec_bool : bool eqDec

val eqDec_ascii : char eqDec

val eqDec_string : char list eqDec

val eqDec_nat : int eqDec

type index = int

val index_of_nat : int -> int -> index option

val index_to_nat : int -> index -> int

val index_of_nat_lt : int -> int -> index

type ('a, 'b) vect_cons_t = { vhd : 'a; vtl : 'b }

type 't vect = __

val vect_hd : int -> ('a1, __) vect_cons_t -> 'a1

val vect_tl : int -> ('a1, __) vect_cons_t -> 'a1 vect

val vect_cons : int -> 'a1 -> 'a1 vect -> ('a1, __) vect_cons_t

val vect_const : int -> 'a1 -> 'a1 vect

val vect_app : int -> int -> 'a1 vect -> 'a1 vect -> 'a1 vect

val vect_split : int -> int -> 'a1 vect -> 'a1 vect * 'a1 vect

val vect_nth : int -> 'a1 vect -> index -> 'a1

val vect_map : int -> ('a1 -> 'a2) -> 'a1 vect -> 'a2 vect

val vect_fold_left : int -> ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 vect -> 'a1

val vect_find_index : int -> ('a1 -> bool) -> 'a1 vect -> index option

val vect_index : int -> 'a1 eqDec -> 'a1 -> 'a1 vect -> index option

val vect_to_list : int -> 'a1 vect -> 'a1 list

val eqDec_vect_nil : 'a1 eqDec -> __ eqDec

val eqDec_vect_cons : 'a1 eqDec -> 'a2 eqDec -> ('a1, 'a2) vect_cons_t eqDec

val eqDec_vect : int -> 'a1 eqDec -> 'a1 vect eqDec

val pow2 : int -> int

module Bits :
 sig
  val rmul : int -> int -> int

  val splitn : int -> int -> bool vect -> bool vect vect

  val appn : int -> int -> bool vect vect -> bool vect

  val neg : int -> bool vect -> bool vect

  val to_N : int -> bool vect -> int

  val to_nat : int -> bool vect -> int

  val of_positive : int -> int -> bool vect

  val of_N : int -> int -> bool vect

  val of_nat : int -> int -> bool vect

  val of_index : int -> int -> index -> bool vect

  val to_index_safe : int -> bool vect -> index

  val zero : int -> bool vect
 end

type 't finiteType = { finite_index : ('t -> int); finite_elements : 't list }

type 'a show = { show0 : ('a -> char list) }

module Show_nat :
 sig
  val string_of_base10_digit : int sig0 -> char list

  val string_of_nat_rec : int -> int -> char list

  val string_of_nat : int -> char list
 end

val show_nat : int show

val show_string : char list show

val eqDec_FiniteType : 'a1 finiteType -> 'a1 eqDec

val list_sum' : int -> int list -> int

val list_sum : int list -> int

val dedup : 'a1 eqDec -> 'a1 list -> 'a1 list -> 'a1 list

type ('s, 'f) result =
| Success of 's
| Failure of 'f

val result_map_failure :
  ('a2 -> 'a3) -> ('a1, 'a2) result -> ('a1, 'a3) result

val opt_result : 'a1 option -> 'a2 -> ('a1, 'a2) result

val result_list_map :
  ('a1 -> ('a2, 'a3) result) -> 'a1 list -> ('a2 list, 'a3) result

val extract_success : ('a1, 'a2) result -> 'a1

type 'k member =
| MemberHd of 'k * 'k list
| MemberTl of 'k * 'k * 'k list * 'k member

val mdestruct : 'a1 list -> 'a1 -> 'a1 member -> __

val nth_member : 'a1 list -> int -> 'a1 -> 'a1 member

val member_map : ('a1 -> 'a2) -> 'a1 -> 'a1 list -> 'a1 member -> 'a2 member

val assoc :
  'a1 eqDec -> 'a1 -> ('a1 * 'a2) list -> ('a2, ('a1 * 'a2) member) sigT
  option

val mprefix : 'a1 list -> 'a1 list -> 'a1 -> 'a1 member -> 'a1 member

val minfix :
  'a1 list -> 'a1 list -> 'a1 list -> 'a1 -> 'a1 member -> 'a1 member

val all_indices : int -> index vect

val finiteType_index : int -> index finiteType

val list_assoc : 'a1 eqDec -> 'a1 -> ('a1 * 'a2) list -> index option

val list_nth : 'a1 list -> index -> 'a1

val show_index : int -> index show

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

type type_kind =
| Kind_bits
| Kind_enum of enum_sig option
| Kind_struct of type0 struct_sig' option
| Kind_array of type0 array_sig' option

val kind_of_type : type0 -> type_kind

val struct_fields_sz' : (type0 -> int) -> (char list * type0) list -> int

val type_sz : type0 -> int

type struct_index = index

val struct_sz : type0 struct_sig' -> int

val field_type : type0 struct_sig' -> index -> type0

val field_sz : type0 struct_sig' -> index -> int

val field_offset_right : type0 struct_sig' -> struct_index -> int

type array_index = index

val array_sz : type0 array_sig' -> int

val element_sz : type0 array_sig' -> int

val element_offset_right : type0 array_sig' -> array_index -> int

type port =
| P0
| P1

type type_denote = __

val bits_of_value : type0 -> type_denote -> bool vect

val value_of_bits : type0 -> bool vect -> type_denote

type 'argKind _Sig = { argSigs : 'argKind vect; retSig : 'argKind }

val cSig_of_Sig : int -> type0 _Sig -> int _Sig

val sig_of_CSig : int -> int _Sig -> type0 _Sig

type externalSignature = type0 _Sig

type cExternalSignature = int _Sig

type 'var_t tsig = ('var_t * type0) list

type lsig = int list

type ('var_t, 'fn_name_t, 'action) internalFunction = { int_name : 'fn_name_t;
                                                        int_argspec : 
                                                        'var_t tsig;
                                                        int_retSig : 
                                                        type0;
                                                        int_body : 'action }

val map_intf_body :
  ('a3 -> 'a4) -> ('a1, 'a2, 'a3) internalFunction -> ('a1, 'a2, 'a4)
  internalFunction

type 'var_t arg_sig = { arg_name : 'var_t; arg_type : type0 }

val prod_of_argsig : 'a1 arg_sig -> 'a1 * type0

val type_id : type0 -> char list

val eqDec_type : type0 eqDec

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

val cmap :
  ('a1 -> 'a2) -> ('a1 -> 'a3 -> 'a4) -> 'a1 list -> ('a1, 'a3) context ->
  ('a2, 'a4) context

type 'k env = { getenv : (__ -> __ -> 'k -> __);
                putenv : (__ -> __ -> 'k -> __ -> __);
                create : (__ -> ('k -> __) -> __); finite_keys : 'k finiteType }

type ('k, 'v) env_t = __

val getenv : 'a1 env -> ('a1, 'a2) env_t -> 'a1 -> 'a2

val putenv : 'a1 env -> ('a1, 'a2) env_t -> 'a1 -> 'a2 -> ('a1, 'a2) env_t

val create : 'a1 env -> ('a1 -> 'a2) -> ('a1, 'a2) env_t

val map0 :
  'a1 env -> ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) env_t -> ('a1, 'a3) env_t

val zip :
  'a1 env -> ('a1, 'a2) env_t -> ('a1, 'a3) env_t -> ('a1, 'a2 * 'a3) env_t

val map2 :
  'a1 env -> ('a1 -> 'a2 -> 'a3 -> 'a4) -> ('a1, 'a2) env_t -> ('a1, 'a3)
  env_t -> ('a1, 'a4) env_t

val fold_right0 :
  'a1 env -> ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) env_t -> 'a3 -> 'a3

val finite_member : 'a1 finiteType -> 'a1 -> 'a1 member

val contextEnv : 'a1 finiteType -> 'a1 env

type basic_error_message =
| OutOfBounds of int * type0 array_sig'
| UnboundField of char list * type0 struct_sig'
| TypeMismatch of type0 * type0
| KindMismatch of type_kind * type_kind

type ('var_t, 'fn_name_t) error_message =
| ExplicitErrorInAst
| SugaredConstructorInAst
| UnboundVariable of 'var_t
| UnboundEnumMember of char list * enum_sig
| BasicError of basic_error_message
| TooManyArguments of 'fn_name_t * int * int
| TooFewArguments of 'fn_name_t * int * int

type fn_tc_error_loc =
| Arg1
| Arg2

type fn_tc_error = fn_tc_error_loc * basic_error_message

val assert_kind :
  type_kind -> fn_tc_error_loc -> type0 -> (__, fn_tc_error) result

type ('pos_t, 'var_t, 'fn_name_t) error = { epos : 'pos_t;
                                            emsg : ('var_t, 'fn_name_t)
                                                   error_message }

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

module PrimUntyped :
 sig
  type udisplay =
  | UDisplayUtf8
  | UDisplayValue of display_options

  type uconv =
  | UPack
  | UUnpack of type0
  | UIgnore

  type ubits1 =
  | UNot
  | USExt of int
  | UZExtL of int
  | UZExtR of int
  | URepeat of int
  | USlice of int * int

  type ubits2 =
  | UAnd
  | UOr
  | UXor
  | ULsl
  | ULsr
  | UAsr
  | UConcat
  | USel
  | USliceSubst of int * int
  | UIndexedSlice of int
  | UPlus
  | UMinus
  | UMul
  | UCompare of bool * bits_comparison

  type ustruct1 =
  | UGetField of char list
  | UGetFieldBits of type0 struct_sig' * char list

  type ustruct2 =
  | USubstField of char list
  | USubstFieldBits of type0 struct_sig' * char list

  type uarray1 =
  | UGetElement of int
  | UGetElementBits of type0 array_sig' * int

  type uarray2 =
  | USubstElement of int
  | USubstElementBits of type0 array_sig' * int

  type ufn1 =
  | UDisplay of udisplay
  | UConv of uconv
  | UBits1 of ubits1
  | UStruct1 of ustruct1
  | UArray1 of uarray1

  type ufn2 =
  | UEq of bool
  | UBits2 of ubits2
  | UStruct2 of ustruct2
  | UArray2 of uarray2
 end

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

  val coq_GetElementBits : type0 array_sig' -> array_index -> fbits1

  val coq_SubstElementBits : type0 array_sig' -> array_index -> fbits2

  val coq_GetFieldBits : type0 struct_sig' -> struct_index -> fbits1

  val coq_SubstFieldBits : type0 struct_sig' -> struct_index -> fbits2
 end

module PrimTypeInference :
 sig
  val find_field :
    type0 struct_sig' -> char list -> (index, fn_tc_error) result

  val check_index :
    type0 array_sig' -> int -> (array_index, fn_tc_error) result

  val tc1 : PrimUntyped.ufn1 -> type0 -> (PrimTyped.fn1, fn_tc_error) result

  val tc2 :
    PrimUntyped.ufn2 -> type0 -> type0 -> (PrimTyped.fn2, fn_tc_error) result
 end

module CircuitSignatures :
 sig
  val coq_DisplaySigma : PrimTyped.fdisplay -> type0 _Sig

  val coq_CSigma1 : PrimTyped.fbits1 -> int _Sig

  val coq_CSigma2 : PrimTyped.fbits2 -> int _Sig
 end

module PrimSignatures :
 sig
  val coq_Sigma1 : PrimTyped.fn1 -> type0 _Sig

  val coq_Sigma2 : PrimTyped.fn2 -> type0 _Sig
 end

type ('from, 'to0) lift = 'from -> 'to0

type ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction =
| UError of ('pos_t, 'var_t, 'fn_name_t) error
| UFail of type0
| UVar of 'var_t
| UConst of type0 * type_denote
| UAssign of 'var_t * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| USeq of ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| UBind of 'var_t * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| UIf of ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| URead of port * 'reg_t
| UWrite of port * 'reg_t
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| UUnop of PrimUntyped.ufn1
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| UBinop of PrimUntyped.ufn2
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| UExternalCall of 'ext_fn_t
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| UInternalCall of ('var_t, 'fn_name_t, ('pos_t, 'var_t, 'fn_name_t, 'reg_t,
                   'ext_fn_t) uaction) internalFunction
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction list
| UAPos of 'pos_t * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| USugar of ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) usugar
and ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) usugar =
| UErrorInAst
| USkip
| UConstBits of int * bool vect
| UConstString of char list
| UConstEnum of enum_sig * char list
| UProgn of ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction list
| ULet of ('var_t * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction)
          list * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| UWhen of ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| USwitch of ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
   * (('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction * ('pos_t,
     'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction) list
| UStructInit of type0 struct_sig'
   * (char list * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction)
     list
| UArrayInit of type0
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction list
| UCallModule of __ finiteType * (__ -> 'reg_t) * (__, 'ext_fn_t) lift
   * ('var_t, 'fn_name_t, ('pos_t, 'var_t, 'fn_name_t, __, __) uaction)
     internalFunction
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction list

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

type ('pos_t, 'var_t, 'reg_t, 'ext_fn_t) action0 =
| Fail0 of lsig * int
| Var0 of int list * 'var_t * int * int member
| Const0 of lsig * int * bool vect
| Assign0 of int list * 'var_t * int * int member
   * ('pos_t, 'var_t, 'reg_t, 'ext_fn_t) action0
| Seq0 of lsig * int * ('pos_t, 'var_t, 'reg_t, 'ext_fn_t) action0
   * ('pos_t, 'var_t, 'reg_t, 'ext_fn_t) action0
| Bind0 of lsig * 'var_t * int * int
   * ('pos_t, 'var_t, 'reg_t, 'ext_fn_t) action0
   * ('pos_t, 'var_t, 'reg_t, 'ext_fn_t) action0
| If0 of lsig * int * ('pos_t, 'var_t, 'reg_t, 'ext_fn_t) action0
   * ('pos_t, 'var_t, 'reg_t, 'ext_fn_t) action0
   * ('pos_t, 'var_t, 'reg_t, 'ext_fn_t) action0
| Read0 of lsig * port * 'reg_t
| Write0 of lsig * port * 'reg_t * ('pos_t, 'var_t, 'reg_t, 'ext_fn_t) action0
| Unop0 of lsig * PrimTyped.fbits1
   * ('pos_t, 'var_t, 'reg_t, 'ext_fn_t) action0
| Binop0 of lsig * PrimTyped.fbits2
   * ('pos_t, 'var_t, 'reg_t, 'ext_fn_t) action0
   * ('pos_t, 'var_t, 'reg_t, 'ext_fn_t) action0
| ExternalCall0 of lsig * 'ext_fn_t
   * ('pos_t, 'var_t, 'reg_t, 'ext_fn_t) action0
| APos0 of lsig * int * 'pos_t * ('pos_t, 'var_t, 'reg_t, 'ext_fn_t) action0

type ('pos_t, 'var_t, 'reg_t, 'ext_fn_t) rule0 =
  ('pos_t, 'var_t, 'reg_t, 'ext_fn_t) action0

val bits_of_ascii :
  char -> (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, __)
  vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
  vect_cons_t) vect_cons_t) vect_cons_t

val array_of_bytes :
  char list -> (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, __)
  vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
  vect_cons_t) vect_cons_t) vect_cons_t vect

val uprogn :
  ('a1, 'a2, 'a3, 'a4, 'a5) uaction list -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction

val uskip : ('a1, 'a2, 'a3, 'a4, 'a5) uaction

val uinit : type0 -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction

val ustruct_init :
  type0 struct_sig' -> (char list * ('a1, 'a2, 'a3, 'a4, 'a5) uaction) list
  -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction

val uswitch :
  ('a1, 'a2, 'a3, 'a4, 'a5) uaction -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction ->
  (('a1, 'a2, 'a3, 'a4, 'a5) uaction * ('a1, 'a2, 'a3, 'a4, 'a5) uaction)
  list -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction

val uswitch_nodefault :
  ('a1, 'a2, 'a3, 'a4, 'a5) uaction -> int -> (('a1, 'a2, 'a3, 'a4, 'a5)
  uaction * ('a1, 'a2, 'a3, 'a4, 'a5) uaction, __) vect_cons_t -> ('a1, 'a2,
  'a3, 'a4, 'a5) uaction

val gen_branches :
  int -> int -> (index -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction) -> (('a1, 'a2,
  'a3, 'a4, 'a5) uaction * ('a1, 'a2, 'a3, 'a4, 'a5) uaction) vect

val uswitch_stateful :
  ('a1, 'a2, 'a3, 'a4, 'a5) uaction -> int -> (('a1, 'a2, 'a3, 'a4, 'a5)
  uaction * ('a1, 'a2, 'a3, 'a4, 'a5) uaction) vect -> ('a1, 'a2, 'a3, 'a4,
  'a5) uaction

val muxtree :
  int -> int -> 'a2 -> int -> (bool vect -> ('a1, 'a2, 'a3, 'a4, 'a5)
  uaction) -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction

val uCompleteMuxTree :
  int -> 'a2 -> (bool vect -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction) -> ('a1,
  'a2, 'a3, 'a4, 'a5) uaction

val ortree :
  int -> (bool vect -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction) -> ('a1, 'a2, 'a3,
  'a4, 'a5) uaction

val uCompleteOrTree :
  int -> int -> 'a2 -> (bool vect -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction) ->
  ('a1, 'a2, 'a3, 'a4, 'a5) uaction

type 'var_t switch_style =
| TreeSwitch
| OrTreeSwitch of int
| NestedSwitch
| SequentialSwitchTt
| SequentialSwitch of type0 * 'var_t

val uCompleteSwitch :
  'a2 switch_style -> int -> 'a2 -> (index -> ('a1, 'a2, 'a3, 'a4, 'a5)
  uaction) -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction

val infix_action :
  ('a3 -> int) -> ('a4 -> cExternalSignature) -> lsig -> lsig -> lsig -> int
  -> ('a1, 'a2, 'a3, 'a4) action0 -> ('a1, 'a2, 'a3, 'a4) action0

val prefix_action :
  ('a3 -> int) -> ('a4 -> cExternalSignature) -> lsig -> lsig -> int -> ('a1,
  'a2, 'a3, 'a4) action0 -> ('a1, 'a2, 'a3, 'a4) action0

val suffix_action :
  ('a3 -> int) -> ('a4 -> cExternalSignature) -> lsig -> lsig -> int -> ('a1,
  'a2, 'a3, 'a4) action0 -> ('a1, 'a2, 'a3, 'a4) action0

val lsig_of_tsig : 'a1 tsig -> lsig

val internalCall' :
  ('a3 -> int) -> ('a4 -> cExternalSignature) -> int -> lsig -> lsig -> (int,
  'a2 * ('a1, 'a2, 'a3, 'a4) action0) context -> ('a1, 'a2, 'a3, 'a4) action0
  -> ('a1, 'a2, 'a3, 'a4) action0

val internalCall :
  ('a3 -> int) -> ('a4 -> cExternalSignature) -> int -> lsig -> lsig -> (int,
  'a2 * ('a1, 'a2, 'a3, 'a4) action0) context -> ('a1, 'a2, 'a3, 'a4) action0
  -> ('a1, 'a2, 'a3, 'a4) action0

val desugar_action' :
  'a1 -> ('a6 -> 'a4) -> ('a7 -> 'a5) -> ('a1, 'a2, 'a3, 'a6, 'a7) uaction ->
  ('a1, 'a2, 'a3, 'a4, 'a5) uaction

val desugar_action :
  'a1 -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction -> ('a1, 'a2, 'a3, 'a4, 'a5)
  uaction

val lift_basic_error_message :
  ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a1 -> 'a2 tsig -> type0 ->
  ('a1, 'a2, 'a3, 'a4, 'a5) action -> basic_error_message -> ('a1, 'a2, 'a3)
  error

val lift_fn1_tc_result :
  ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a2 tsig -> type0 -> 'a1 ->
  ('a1, 'a2, 'a3, 'a4, 'a5) action -> ('a6, fn_tc_error) result -> ('a6,
  ('a1, 'a2, 'a3) error) result

val lift_fn2_tc_result :
  ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a2 tsig -> type0 -> 'a2
  tsig -> type0 -> 'a1 -> ('a1, 'a2, 'a3, 'a4, 'a5) action -> 'a1 -> ('a1,
  'a2, 'a3, 'a4, 'a5) action -> ('a6, fn_tc_error) result -> ('a6, ('a1, 'a2,
  'a3) error) result

val mkerror : 'a1 -> ('a3, 'a2) error_message -> 'a4 -> ('a1, 'a3, 'a2) error

val cast_action' :
  ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a1 -> 'a3 tsig -> type0 ->
  type0 -> ('a1, 'a3, 'a2, 'a4, 'a5) action -> ('a3, 'a2) error_message ->
  (('a1, 'a3, 'a2, 'a4, 'a5) action, ('a1, 'a3, 'a2) error) result

val cast_action :
  ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a1 -> 'a3 tsig -> type0 ->
  type0 -> ('a1, 'a3, 'a2, 'a4, 'a5) action -> (('a1, 'a3, 'a2, 'a4, 'a5)
  action, ('a1, 'a3, 'a2) error) result

val actpos : 'a1 -> ('a1, 'a3, 'a2, 'a4, 'a5) uaction -> 'a1

val assert_argtypes' :
  ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a3 tsig -> 'a6 -> int ->
  'a2 -> 'a1 -> 'a3 tsig -> ('a1 * (type0, ('a1, 'a3, 'a2, 'a4, 'a5) action)
  sigT) list -> (('a3 * type0, ('a1, 'a3, 'a2, 'a4, 'a5) action) context,
  ('a1, 'a3, 'a2) error) result

val assert_argtypes :
  ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a3 tsig -> 'a6 -> 'a2 ->
  'a1 -> 'a3 tsig -> ('a1 * (type0, ('a1, 'a3, 'a2, 'a4, 'a5) action) sigT)
  list -> (('a3 * type0, ('a1, 'a3, 'a2, 'a4, 'a5) action) context, ('a1,
  'a3, 'a2) error) result

val type_action :
  'a3 eqDec -> ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a1 -> 'a3
  tsig -> ('a1, 'a3, 'a2, 'a4, 'a5) uaction -> ((type0, ('a1, 'a3, 'a2, 'a4,
  'a5) action) sigT, ('a1, 'a3, 'a2) error) result

val tc_action :
  'a3 eqDec -> ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a1 -> 'a3
  tsig -> type0 -> ('a1, 'a3, 'a2, 'a4, 'a5) uaction -> (('a1, 'a3, 'a2, 'a4,
  'a5) action, ('a1, 'a3, 'a2) error) result

type rwdata_field =
| Rwdata_r0
| Rwdata_r1
| Rwdata_w0
| Rwdata_w1
| Rwdata_data0
| Rwdata_data1

type 'reg_t rwcircuit_field =
| Rwcircuit_rwdata of 'reg_t * rwdata_field
| Rwcircuit_canfire

type ('rule_name_t, 'reg_t, 'ext_fn_t, 'rwdata) circuit =
| CMux of int * ('rule_name_t, 'reg_t, 'ext_fn_t, 'rwdata) circuit
   * ('rule_name_t, 'reg_t, 'ext_fn_t, 'rwdata) circuit
   * ('rule_name_t, 'reg_t, 'ext_fn_t, 'rwdata) circuit
| CConst of int * bool vect
| CReadRegister of 'reg_t
| CUnop of PrimTyped.fbits1
   * ('rule_name_t, 'reg_t, 'ext_fn_t, 'rwdata) circuit
| CBinop of PrimTyped.fbits2
   * ('rule_name_t, 'reg_t, 'ext_fn_t, 'rwdata) circuit
   * ('rule_name_t, 'reg_t, 'ext_fn_t, 'rwdata) circuit
| CExternal of 'ext_fn_t * ('rule_name_t, 'reg_t, 'ext_fn_t, 'rwdata) circuit
| CBundleRef of int * 'rule_name_t * 'reg_t list * ('reg_t, 'rwdata) context
   * 'reg_t rwcircuit_field
   * ('rule_name_t, 'reg_t, 'ext_fn_t, 'rwdata) circuit
| CAnnot of int * char list
   * ('rule_name_t, 'reg_t, 'ext_fn_t, 'rwdata) circuit

val unannot :
  int -> ('a1, 'a2, 'a3, 'a4) circuit -> ('a1, 'a2, 'a3, 'a4) circuit

val asconst :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> int -> ('a1, 'a2, 'a3, 'a4)
  circuit -> bool vect option

val isconst :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> int -> ('a1, 'a2, 'a3, 'a4)
  circuit -> bool vect -> bool

val opt_constprop' :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> int -> ('a1, 'a2, 'a3, 'a4)
  circuit -> ('a1, 'a2, 'a3, 'a4) circuit

val opt_mux_bit1 :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> int -> ('a1, 'a2, 'a3, 'a4)
  circuit -> ('a1, 'a2, 'a3, 'a4) circuit

val opt_constprop :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> int -> ('a1, 'a2, 'a3, 'a4)
  circuit -> ('a1, 'a2, 'a3, 'a4) circuit

type lRW =
| LRWRead
| LRWWrite

val action_footprint' :
  ('a3 * (lRW * port)) list -> ('a1, 'a2, 'a3, 'a4) action0 ->
  ('a3 * (lRW * port)) list

val action_footprint :
  ('a1, 'a2, 'a3, 'a4) action0 -> ('a3 * (lRW * port)) list

val action_registers :
  ('a3 -> int) -> ('a4 -> cExternalSignature) -> lsig -> int -> 'a3 eqDec ->
  ('a1, 'a2, 'a3, 'a4) action0 -> 'a3 list

type ('rule_name_t, 'reg_t, 'ext_fn_t) rwdata = { read0 : ('rule_name_t,
                                                          'reg_t, 'ext_fn_t,
                                                          ('rule_name_t,
                                                          'reg_t, 'ext_fn_t)
                                                          rwdata) circuit;
                                                  read1 : ('rule_name_t,
                                                          'reg_t, 'ext_fn_t,
                                                          ('rule_name_t,
                                                          'reg_t, 'ext_fn_t)
                                                          rwdata) circuit;
                                                  write0 : ('rule_name_t,
                                                           'reg_t, 'ext_fn_t,
                                                           ('rule_name_t,
                                                           'reg_t, 'ext_fn_t)
                                                           rwdata) circuit;
                                                  write1 : ('rule_name_t,
                                                           'reg_t, 'ext_fn_t,
                                                           ('rule_name_t,
                                                           'reg_t, 'ext_fn_t)
                                                           rwdata) circuit;
                                                  data0 : ('rule_name_t,
                                                          'reg_t, 'ext_fn_t,
                                                          ('rule_name_t,
                                                          'reg_t, 'ext_fn_t)
                                                          rwdata) circuit;
                                                  data1 : ('rule_name_t,
                                                          'reg_t, 'ext_fn_t,
                                                          ('rule_name_t,
                                                          'reg_t, 'ext_fn_t)
                                                          rwdata) circuit }

val readRegisters :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 -> ('a1, 'a2, 'a3, ('a1,
  'a2, 'a3) rwdata) circuit

type ('rule_name_t, 'reg_t, 'ext_fn_t) rwset =
  ('reg_t, ('rule_name_t, 'reg_t, 'ext_fn_t) rwdata) env_t

type ('rule_name_t, 'reg_t, 'ext_fn_t) rwcircuit = { canFire : ('rule_name_t,
                                                               'reg_t,
                                                               'ext_fn_t,
                                                               ('rule_name_t,
                                                               'reg_t,
                                                               'ext_fn_t)
                                                               rwdata) circuit;
                                                     regs : ('rule_name_t,
                                                            'reg_t,
                                                            'ext_fn_t) rwset }

type ('rule_name_t, 'reg_t, 'ext_fn_t) action_circuit = { erwc : ('rule_name_t,
                                                                 'reg_t,
                                                                 'ext_fn_t)
                                                                 rwcircuit;
                                                          retVal : ('rule_name_t,
                                                                   'reg_t,
                                                                   'ext_fn_t,
                                                                   ('rule_name_t,
                                                                   'reg_t,
                                                                   'ext_fn_t)
                                                                   rwdata)
                                                                   circuit }

type ('rule_name_t, 'reg_t, 'ext_fn_t) scheduler_circuit =
  ('rule_name_t, 'reg_t, 'ext_fn_t) rwset

type ('rule_name_t, 'reg_t, 'ext_fn_t) ccontext =
  (int, ('rule_name_t, 'reg_t, 'ext_fn_t, ('rule_name_t, 'reg_t, 'ext_fn_t)
  rwdata) circuit) context

val mux_rwdata :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
  ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
  circuit) -> int -> char list -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
  circuit -> ('a1, 'a2, 'a3) rwdata -> ('a1, 'a2, 'a3) rwdata -> ('a1, 'a2,
  'a3) rwdata

val mux_rwsets :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> (int -> ('a1,
  'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2,
  'a3) rwdata) circuit) -> char list -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3)
  rwdata) circuit -> ('a1, 'a2, 'a3) rwset -> ('a1, 'a2, 'a3) rwset -> ('a2,
  ('a1, 'a2, 'a3) rwdata) env_t

val mux_ccontext :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
  ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
  circuit) -> lsig -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit ->
  ('a1, 'a2, 'a3) ccontext -> ('a1, 'a2, 'a3) ccontext -> ('a1, 'a2, 'a3)
  ccontext

val compile_unop :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
  ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
  circuit) -> PrimTyped.fbits1 -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
  circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit

val slice_subst_macro :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
  ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
  circuit) -> int -> int -> int -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
  circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2,
  'a3, ('a1, 'a2, 'a3) rwdata) circuit

val compile_binop :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
  ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
  circuit) -> PrimTyped.fbits2 -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
  circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2,
  'a3, ('a1, 'a2, 'a3) rwdata) circuit

val compile_action :
  ('a4 -> int) -> ('a5 -> cExternalSignature) -> 'a4 env -> 'a2 show -> (int
  -> ('a3, 'a4, 'a5, ('a3, 'a4, 'a5) rwdata) circuit -> ('a3, 'a4, 'a5, ('a3,
  'a4, 'a5) rwdata) circuit) -> ('a4, ('a3, 'a4, 'a5, ('a3, 'a4, 'a5) rwdata)
  circuit) env_t -> lsig -> int -> ('a3, 'a4, 'a5) ccontext -> ('a1, 'a2,
  'a4, 'a5) action0 -> ('a3, 'a4, 'a5) rwcircuit -> ('a3, 'a4, 'a5)
  action_circuit * ('a3, 'a4, 'a5) ccontext

val adapter :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> (int -> ('a1,
  'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2,
  'a3) rwdata) circuit) -> ('a1, 'a2, 'a3) scheduler_circuit -> ('a1, 'a2,
  'a3) rwcircuit

val willFire_of_canFire'_read0 :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
  ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
  circuit) -> int -> ('a1, 'a2, 'a3) rwdata -> ('a1, 'a2, 'a3) rwdata ->
  ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit

val willFire_of_canFire'_write0 :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
  ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
  circuit) -> int -> ('a1, 'a2, 'a3) rwdata -> ('a1, 'a2, 'a3) rwdata ->
  ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit

val willFire_of_canFire'_rw1 :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
  ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
  circuit) -> int -> ('a1, 'a2, 'a3) rwdata -> ('a1, 'a2, 'a3) rwdata ->
  ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit

val willFire_of_canFire' :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
  ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
  circuit) -> int -> ('a1, 'a2, 'a3) rwdata -> ('a1, 'a2, 'a3) rwdata ->
  ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit

val willFire_of_canFire :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> 'a1 show -> (int
  -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1,
  'a2, 'a3) rwdata) circuit) -> 'a1 -> ('a1, 'a2, 'a3) rwcircuit -> ('a2,
  ('a1, 'a2, 'a3) rwdata) env_t -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
  circuit

val update_accumulated_rwset :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> (int -> ('a1,
  'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2,
  'a3) rwdata) circuit) -> ('a1, 'a2, 'a3) rwset -> ('a1, 'a2, 'a3) rwset ->
  ('a2, ('a1, 'a2, 'a3) rwdata) env_t

val bundleref_wrap_rwdata :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> 'a1 -> 'a2 list
  -> ('a2, ('a1, 'a2, 'a3) rwdata) context -> 'a2 -> ('a1, 'a2, 'a3) rwdata
  -> ('a1, 'a2, 'a3) rwdata

val bundleref_wrap_rwset :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> 'a1 -> 'a2 list
  -> ('a2, ('a1, 'a2, 'a3) rwdata) context -> ('a1, 'a2, 'a3) rwset -> ('a2,
  ('a1, 'a2, 'a3) rwdata) env_t

val bundleref_wrap_erwc :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> 'a1 -> 'a2 list
  -> ('a2, ('a1, 'a2, 'a3) rwdata) context -> ('a1, 'a2, 'a3) rwcircuit ->
  ('a1, 'a2, 'a3) rwcircuit

val bundleref_wrap_action_circuit :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> int -> 'a2 list
  -> ('a1, 'a2, 'a3) rwset -> ('a1, 'a2, 'a3) action_circuit -> 'a1 -> ('a1,
  'a2, 'a3) action_circuit

val compile_scheduler_circuit :
  ('a4 -> int) -> ('a5 -> cExternalSignature) -> 'a4 env -> 'a2 show -> 'a3
  show -> (int -> ('a3, 'a4, 'a5, ('a3, 'a4, 'a5) rwdata) circuit -> ('a3,
  'a4, 'a5, ('a3, 'a4, 'a5) rwdata) circuit) -> ('a4, ('a3, 'a4, 'a5, ('a3,
  'a4, 'a5) rwdata) circuit) env_t -> ('a3 -> ('a1, 'a2, 'a4, 'a5) rule0) ->
  ('a3 -> bool) -> ('a1, 'a3) scheduler -> ('a3, 'a4, 'a5) scheduler_circuit
  -> ('a3, 'a4, 'a5) scheduler_circuit

val commit_rwdata :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
  ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
  circuit) -> int -> ('a1, 'a2, 'a3) rwdata -> ('a1, 'a2, 'a3, ('a1, 'a2,
  'a3) rwdata) circuit

val init_scheduler_rwdata :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> (int -> ('a1,
  'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2,
  'a3) rwdata) circuit) -> ('a2, ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
  circuit) env_t -> 'a2 -> ('a1, 'a2, 'a3) rwdata

val init_scheduler_circuit :
  ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> (int -> ('a1,
  'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2,
  'a3) rwdata) circuit) -> ('a2, ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
  circuit) env_t -> ('a1, 'a2, 'a3) scheduler_circuit

type ('rule_name_t, 'reg_t, 'ext_fn_t) register_update_circuitry =
  ('reg_t, ('rule_name_t, 'reg_t, 'ext_fn_t, ('rule_name_t, 'reg_t,
  'ext_fn_t) rwdata) circuit) env_t

val compile_scheduler' :
  ('a4 -> int) -> ('a5 -> cExternalSignature) -> 'a4 env -> 'a2 show -> 'a3
  show -> (int -> ('a3, 'a4, 'a5, ('a3, 'a4, 'a5) rwdata) circuit -> ('a3,
  'a4, 'a5, ('a3, 'a4, 'a5) rwdata) circuit) -> ('a4, ('a3, 'a4, 'a5, ('a3,
  'a4, 'a5) rwdata) circuit) env_t -> ('a3 -> ('a1, 'a2, 'a4, 'a5) rule0) ->
  ('a3 -> bool) -> ('a1, 'a3) scheduler -> ('a3, 'a4, 'a5)
  register_update_circuitry

val lower_R : ('a1 -> type0) -> 'a1 -> int

val lower_Sigma : ('a1 -> externalSignature) -> 'a1 -> int _Sig

val lower_unop :
  ('a3 -> type0) -> ('a4 -> externalSignature) -> lsig -> PrimTyped.fn1 ->
  ('a1, 'a2, 'a3, 'a4) action0 -> ('a1, 'a2, 'a3, 'a4) action0

val lower_binop :
  ('a3 -> type0) -> ('a4 -> externalSignature) -> lsig -> PrimTyped.fn2 ->
  ('a1, 'a2, 'a3, 'a4) action0 -> ('a1, 'a2, 'a3, 'a4) action0 -> ('a1, 'a2,
  'a3, 'a4) action0

val lower_member :
  'a1 -> type0 -> ('a1 * type0) list -> ('a1 * type0) member -> int member

val lower_args' :
  ('a4 -> type0) -> ('a5 -> externalSignature) -> ('a2 tsig -> type0 -> ('a1,
  'a2, 'a3, 'a4, 'a5) action -> ('a1, 'a2, 'a4, 'a5) action0) -> 'a2 tsig ->
  ('a2 * type0) list -> ('a2 * type0, ('a1, 'a2, 'a3, 'a4, 'a5) action)
  context -> (int, 'a2 * ('a1, 'a2, 'a4, 'a5) action0) context

val lower_action :
  ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a2 tsig -> type0 -> ('a1,
  'a2, 'a3, 'a4, 'a5) action -> ('a1, 'a2, 'a4, 'a5) action0

val compile_scheduler :
  ('a5 -> type0) -> ('a6 -> externalSignature) -> 'a5 finiteType -> 'a2 show
  -> 'a4 show -> (int -> ('a4, 'a5, 'a6, ('a4, 'a5, 'a6) rwdata) circuit ->
  ('a4, 'a5, 'a6, ('a4, 'a5, 'a6) rwdata) circuit) -> ('a4 -> ('a1, 'a2, 'a3,
  'a5, 'a6) rule) -> ('a4 -> bool) -> ('a1, 'a4) scheduler -> ('a4, 'a5, 'a6)
  register_update_circuitry

type ext_fn_rtl_spec = { efr_name : char list; efr_internal : bool }

type ext_fn_sim_spec = { efs_name : char list; efs_method : bool }

val lift_empty : __ -> 'a1

val lift_self : ('a1, 'a1) lift

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

type 'pos_t dummyPos = { dummy_pos : 'pos_t }

val dummyPos_unit : unit dummyPos

type pos_t = unit

type var_t = char list

type fn_name_t = char list

val maybe : type0 -> type0 struct_sig'

val valid :
  type0 -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, 'a2) uaction)
  internalFunction

val invalid :
  type0 -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, 'a2) uaction)
  internalFunction

module type Fifo =
 sig
  val coq_T : type0
 end

module Fifo1 :
 functor (Coq_f:Fifo) ->
 sig
  type reg_t =
  | Coq_data0
  | Coq_valid0

  val reg_t_rect : 'a1 -> 'a1 -> reg_t -> 'a1

  val reg_t_rec : 'a1 -> 'a1 -> reg_t -> 'a1

  val coq_R : reg_t -> type0

  val r : reg_t -> type_denote

  val name_reg : reg_t -> char list

  val can_enq :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val enq :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val can_deq :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val peek :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val deq :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val coq_FiniteType_reg_t : reg_t finiteType
 end

module Fifo1Bypass :
 functor (Coq_f:Fifo) ->
 sig
  type reg_t =
  | Coq_data0
  | Coq_valid0

  val reg_t_rect : 'a1 -> 'a1 -> reg_t -> 'a1

  val reg_t_rec : 'a1 -> 'a1 -> reg_t -> 'a1

  val coq_R : reg_t -> type0

  val r : reg_t -> type_denote

  val name_reg : reg_t -> char list

  val can_enq :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val enq :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val can_deq :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val peek :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val deq :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val coq_FiniteType_reg_t : reg_t finiteType
 end

module type RfPow2_sig =
 sig
  val idx_sz : int

  val coq_T : type0

  val init : type_denote

  val read_style : var_t switch_style

  val write_style : var_t switch_style
 end

module RfPow2 :
 functor (Coq_s:RfPow2_sig) ->
 sig
  val sz : int

  type reg_t =
  | Coq_rData of index

  val reg_t_rect : (index -> 'a1) -> reg_t -> 'a1

  val reg_t_rec : (index -> 'a1) -> reg_t -> 'a1

  val finite_rf_reg : reg_t finiteType

  val coq_R : reg_t -> type0

  val r : reg_t -> type_denote

  val name_reg : reg_t -> char list

  val read_0 :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val write_0 :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val read_1 :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val write_1 :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction
 end

val signExtend :
  int -> int -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __)
  uaction) internalFunction

val funct3_ADD :
  (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t

val funct7_ADD :
  (bool, (bool, (bool, (bool, (bool, (bool, (bool, __) vect_cons_t)
  vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t

val funct3_SLL :
  (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t

val funct3_SLT :
  (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t

val funct3_SLTU :
  (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t

val funct3_XOR :
  (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t

val funct3_SRL :
  (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t

val funct3_OR : (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t

val funct3_AND :
  (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t

val opcode_BRANCH :
  (bool, (bool, (bool, (bool, (bool, (bool, (bool, __) vect_cons_t)
  vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t

val funct3_BEQ :
  (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t

val funct3_BNE :
  (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t

val funct3_BLT :
  (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t

val funct3_BGE :
  (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t

val funct3_BLTU :
  (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t

val funct3_BGEU :
  (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t

module type Scoreboard_sig =
 sig
  val idx_sz : int

  val maxScore : int
 end

val write_style0 : var_t switch_style

val read_style0 : int -> var_t switch_style

module Scoreboard :
 functor (Coq_s:Scoreboard_sig) ->
 sig
  val sz : int

  val logScore : int

  module RfParams :
   sig
    val idx_sz : int

    val coq_T : type0

    val init : bool vect

    val read_style : var_t switch_style

    val write_style : var_t switch_style
   end

  module Rf :
   sig
    val sz : int

    type reg_t =
    | Coq_rData of index

    val reg_t_rect : (index -> 'a1) -> reg_t -> 'a1

    val reg_t_rec : (index -> 'a1) -> reg_t -> 'a1

    val finite_rf_reg : reg_t finiteType

    val coq_R : reg_t -> type0

    val r : reg_t -> type_denote

    val name_reg : reg_t -> char list

    val read_0 :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val write_0 :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val read_1 :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val write_1 :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction
   end

  type reg_t =
  | Scores of Rf.reg_t

  val reg_t_rect : (Rf.reg_t -> 'a1) -> reg_t -> 'a1

  val reg_t_rec : (Rf.reg_t -> 'a1) -> reg_t -> 'a1

  val coq_R : reg_t -> type0

  val r : reg_t -> type_denote

  val name_reg : reg_t -> char list

  val sat_incr :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val sat_decr :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val finite_rf_reg : Rf.reg_t finiteType

  val finite_reg : reg_t finiteType

  val insert :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val remove :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val search :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction
 end

module ShadowStackF :
 sig
  val capacity : int

  type _reg_t =
  | Coq_size
  | Coq_stack of index

  val _reg_t_rect : 'a1 -> (index -> 'a1) -> _reg_t -> 'a1

  val _reg_t_rec : 'a1 -> (index -> 'a1) -> _reg_t -> 'a1

  type reg_t = _reg_t

  val coq_R : _reg_t -> type0

  val r : _reg_t -> type_denote

  val read_vect_sequential :
    char list -> (pos_t, var_t, fn_name_t, reg_t, __) uaction

  val write0_stack :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val push :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val pop :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val coq_Show_reg_t : reg_t show

  val coq_FiniteType_reg_t : reg_t finiteType
 end

type base_standard =
| RV32I
| RV64I

type extension =
| RVM
| RVA
| RVF
| RVD
| RVQ
| RVZiCSR
| RVZifencei

type iSA = { iSA_base_standard : base_standard;
             iSA_extensions : extension list }

type instruction =
| LUI_32I
| AUIPC_32I
| JAL_32I
| JALR_32I
| BEQ_32I
| BNE_32I
| BLT_32I
| BGE_32I
| BLTU_32I
| BGEU_32I
| LB_32I
| LH_32I
| LW_32I
| LBU_32I
| LHU_32I
| SB_32I
| SH_32I
| SW_32I
| ADDI_32I
| SLTI_32I
| SLTIU_32I
| XORI_32I
| ORI_32I
| ANDI_32I
| SLLI_32I
| SRLI_32I
| SRAI_32I
| ADD_32I
| SUB_32I
| SLL_32I
| SLT_32I
| SLTU_32I
| XOR_32I
| SRL_32I
| SRA_32I
| OR_32I
| AND_32I
| FENCE_32I
| ECALL_32I
| EBREAK_32I
| LUI_64I
| AUIPC_64I
| JAL_64I
| JALR_64I
| BEQ_64I
| BNE_64I
| BLT_64I
| BGE_64I
| BLTU_64I
| BGEU_64I
| LB_64I
| LH_64I
| LW_64I
| LBU_64I
| LHU_64I
| SB_64I
| SH_64I
| SW_64I
| ADDI_64I
| SLTI_64I
| SLTIU_64I
| XORI_64I
| ORI_64I
| ANDI_64I
| SLLI_64I
| SRLI_64I
| SRAI_64I
| ADD_64I
| SUB_64I
| SLL_64I
| SLT_64I
| SLTU_64I
| XOR_64I
| SRL_64I
| SRA_64I
| OR_64I
| AND_64I
| FENCE_64I
| ECALL_64I
| EBREAK_64I
| LWU_64I
| LD_64I
| SD_64I
| ADDIW_64I
| SLLIW_64I
| SRLIW_64I
| SRAIW_64I
| ADDW_64I
| SUBW_64I
| SLLW_64I
| SRLW_64I
| SRAW_64I
| FENCE_I_32Zifencei
| FENCE_I_64Zifencei
| CSRRW_32Zicsr
| CSRRS_32Zicsr
| CSRRC_32Zicsr
| CSRRWI_32Zicsr
| CSRRSI_32Zicsr
| CSRRCI_32Zicsr
| CSRRW_64Zicsr
| CSRRS_64Zicsr
| CSRRC_64Zicsr
| CSRRWI_64Zicsr
| CSRRSI_64Zicsr
| CSRRCI_64Zicsr
| MUL_32M
| MULH_32M
| MULHSU_32M
| MULHU_32M
| DIV_32M
| DIVU_32M
| REM_32M
| REMU_32M
| MUL_64M
| MULH_64M
| MULHSU_64M
| MULHU_64M
| DIV_64M
| DIVU_64M
| REM_64M
| REMU_64M
| MULW_64M
| DIVW_64M
| DIVUW_64M
| REMW_64M
| REMUW_64M
| LR_W_00_32A
| LR_W_01_32A
| LR_W_10_32A
| LR_W_11_32A
| SC_W_00_32A
| SC_W_01_32A
| SC_W_10_32A
| SC_W_11_32A
| AMOSWAP_W_00_32A
| AMOSWAP_W_01_32A
| AMOSWAP_W_10_32A
| AMOSWAP_W_11_32A
| AMOADD_W_00_32A
| AMOADD_W_01_32A
| AMOADD_W_10_32A
| AMOADD_W_11_32A
| AMOXOR_W_00_32A
| AMOXOR_W_01_32A
| AMOXOR_W_10_32A
| AMOXOR_W_11_32A
| AMOAND_W_00_32A
| AMOAND_W_01_32A
| AMOAND_W_10_32A
| AMOAND_W_11_32A
| AMOOR_W_00_32A
| AMOOR_W_01_32A
| AMOOR_W_10_32A
| AMOOR_W_11_32A
| AMOMIN_W_00_32A
| AMOMIN_W_01_32A
| AMOMIN_W_10_32A
| AMOMIN_W_11_32A
| AMOMAX_W_00_32A
| AMOMAX_W_01_32A
| AMOMAX_W_10_32A
| AMOMAX_W_11_32A
| AMOMINU_W_00_32A
| AMOMINU_W_01_32A
| AMOMINU_W_10_32A
| AMOMINU_W_11_32A
| AMOMAXU_W_00_32A
| AMOMAXU_W_01_32A
| AMOMAXU_W_10_32A
| AMOMAXU_W_11_32A
| LR_W_00_64A
| LR_W_01_64A
| LR_W_10_64A
| LR_W_11_64A
| SC_W_00_64A
| SC_W_01_64A
| SC_W_10_64A
| SC_W_11_64A
| AMOSWAP_W_00_64A
| AMOSWAP_W_01_64A
| AMOSWAP_W_10_64A
| AMOSWAP_W_11_64A
| AMOADD_W_00_64A
| AMOADD_W_01_64A
| AMOADD_W_10_64A
| AMOADD_W_11_64A
| AMOXOR_W_00_64A
| AMOXOR_W_01_64A
| AMOXOR_W_10_64A
| AMOXOR_W_11_64A
| AMOAND_W_00_64A
| AMOAND_W_01_64A
| AMOAND_W_10_64A
| AMOAND_W_11_64A
| AMOOR_W_00_64A
| AMOOR_W_01_64A
| AMOOR_W_10_64A
| AMOOR_W_11_64A
| AMOMIN_W_00_64A
| AMOMIN_W_01_64A
| AMOMIN_W_10_64A
| AMOMIN_W_11_64A
| AMOMAX_W_00_64A
| AMOMAX_W_01_64A
| AMOMAX_W_10_64A
| AMOMAX_W_11_64A
| AMOMINU_W_00_64A
| AMOMINU_W_01_64A
| AMOMINU_W_10_64A
| AMOMINU_W_11_64A
| AMOMAXU_W_00_64A
| AMOMAXU_W_01_64A
| AMOMAXU_W_10_64A
| AMOMAXU_W_11_64A
| LR_D_00_64A
| LR_D_01_64A
| LR_D_10_64A
| LR_D_11_64A
| SC_D_00_64A
| SC_D_01_64A
| SC_D_10_64A
| SC_D_11_64A
| AMOSWAP_D_00_64A
| AMOSWAP_D_01_64A
| AMOSWAP_D_10_64A
| AMOSWAP_D_11_64A
| AMOADD_D_00_64A
| AMOADD_D_01_64A
| AMOADD_D_10_64A
| AMOADD_D_11_64A
| AMOXOR_D_00_64A
| AMOXOR_D_01_64A
| AMOXOR_D_10_64A
| AMOXOR_D_11_64A
| AMOAND_D_00_64A
| AMOAND_D_01_64A
| AMOAND_D_10_64A
| AMOAND_D_11_64A
| AMOOR_D_00_64A
| AMOOR_D_01_64A
| AMOOR_D_10_64A
| AMOOR_D_11_64A
| AMOMIN_D_00_64A
| AMOMIN_D_01_64A
| AMOMIN_D_10_64A
| AMOMIN_D_11_64A
| AMOMAX_D_00_64A
| AMOMAX_D_01_64A
| AMOMAX_D_10_64A
| AMOMAX_D_11_64A
| AMOMINU_D_00_64A
| AMOMINU_D_01_64A
| AMOMINU_D_10_64A
| AMOMINU_D_11_64A
| AMOMAXU_D_00_64A
| AMOMAXU_D_01_64A
| AMOMAXU_D_10_64A
| AMOMAXU_D_11_64A
| FLW_32F
| FSW_32F
| FMADD_RNE_S_32F
| FMADD_RTZ_S_32F
| FMADD_RDN_S_32F
| FMADD_RUP_S_32F
| FMADD_RMM_S_32F
| FMADD_DYN_S_32F
| FMSUB_RNE_S_32F
| FMSUB_RTZ_S_32F
| FMSUB_RDN_S_32F
| FMSUB_RUP_S_32F
| FMSUB_RMM_S_32F
| FMSUB_DYN_S_32F
| FNMSUB_RNE_S_32F
| FNMSUB_RTZ_S_32F
| FNMSUB_RDN_S_32F
| FNMSUB_RUP_S_32F
| FNMSUB_RMM_S_32F
| FNMSUB_DYN_S_32F
| FNMADD_RNE_S_32F
| FNMADD_RTZ_S_32F
| FNMADD_RDN_S_32F
| FNMADD_RUP_S_32F
| FNMADD_RMM_S_32F
| FNMADD_DYN_S_32F
| FADD_RNE_S_32F
| FADD_RTZ_S_32F
| FADD_RDN_S_32F
| FADD_RUP_S_32F
| FADD_RMM_S_32F
| FADD_DYN_S_32F
| FSUB_RNE_S_32F
| FSUB_RTZ_S_32F
| FSUB_RDN_S_32F
| FSUB_RUP_S_32F
| FSUB_RMM_S_32F
| FSUB_DYN_S_32F
| FMUL_RNE_S_32F
| FMUL_RTZ_S_32F
| FMUL_RDN_S_32F
| FMUL_RUP_S_32F
| FMUL_RMM_S_32F
| FMUL_DYN_S_32F
| FDIV_RNE_S_32F
| FDIV_RTZ_S_32F
| FDIV_RDN_S_32F
| FDIV_RUP_S_32F
| FDIV_RMM_S_32F
| FDIV_DYN_S_32F
| FSQRT_RNE_S_32F
| FSQRT_RTZ_S_32F
| FSQRT_RDN_S_32F
| FSQRT_RUP_S_32F
| FSQRT_RMM_S_32F
| FSQRT_DYN_S_32F
| FSGNJ_S_32F
| FSGNJN_S_32F
| FSGNJX_S_32F
| FMIN_S_32F
| FMAX_S_32F
| FCVT_RNE_W_S_32F
| FCVT_RTZ_W_S_32F
| FCVT_RDN_W_S_32F
| FCVT_RUP_W_S_32F
| FCVT_RMM_W_S_32F
| FCVT_DYN_W_S_32F
| FCVT_RNE_WU_S_32F
| FCVT_RTZ_WU_S_32F
| FCVT_RDN_WU_S_32F
| FCVT_RUP_WU_S_32F
| FCVT_RMM_WU_S_32F
| FCVT_DYN_WU_S_32F
| FMV_X_W_32F
| FEQ_S_32F
| FLT_S_32F
| FLE_S_32F
| FCLASS_S_32F
| FCVT_RNE_S_W_32F
| FCVT_RTZ_S_W_32F
| FCVT_RDN_S_W_32F
| FCVT_RUP_S_W_32F
| FCVT_RMM_S_W_32F
| FCVT_DYN_S_W_32F
| FCVT_RNE_S_WU_32F
| FCVT_RTZ_S_WU_32F
| FCVT_RDN_S_WU_32F
| FCVT_RUP_S_WU_32F
| FCVT_RMM_S_WU_32F
| FCVT_DYN_S_WU_32F
| FMV_W_X_32F
| FLW_64F
| FSW_64F
| FMADD_RNE_S_64F
| FMADD_RTZ_S_64F
| FMADD_RDN_S_64F
| FMADD_RUP_S_64F
| FMADD_RMM_S_64F
| FMADD_DYN_S_64F
| FMSUB_RNE_S_64F
| FMSUB_RTZ_S_64F
| FMSUB_RDN_S_64F
| FMSUB_RUP_S_64F
| FMSUB_RMM_S_64F
| FMSUB_DYN_S_64F
| FNMSUB_RNE_S_64F
| FNMSUB_RTZ_S_64F
| FNMSUB_RDN_S_64F
| FNMSUB_RUP_S_64F
| FNMSUB_RMM_S_64F
| FNMSUB_DYN_S_64F
| FNMADD_RNE_S_64F
| FNMADD_RTZ_S_64F
| FNMADD_RDN_S_64F
| FNMADD_RUP_S_64F
| FNMADD_RMM_S_64F
| FNMADD_DYN_S_64F
| FADD_RNE_S_64F
| FADD_RTZ_S_64F
| FADD_RDN_S_64F
| FADD_RUP_S_64F
| FADD_RMM_S_64F
| FADD_DYN_S_64F
| FSUB_RNE_S_64F
| FSUB_RTZ_S_64F
| FSUB_RDN_S_64F
| FSUB_RUP_S_64F
| FSUB_RMM_S_64F
| FSUB_DYN_S_64F
| FMUL_RNE_S_64F
| FMUL_RTZ_S_64F
| FMUL_RDN_S_64F
| FMUL_RUP_S_64F
| FMUL_RMM_S_64F
| FMUL_DYN_S_64F
| FDIV_RNE_S_64F
| FDIV_RTZ_S_64F
| FDIV_RDN_S_64F
| FDIV_RUP_S_64F
| FDIV_RMM_S_64F
| FDIV_DYN_S_64F
| FSQRT_RNE_S_64F
| FSQRT_RTZ_S_64F
| FSQRT_RDN_S_64F
| FSQRT_RUP_S_64F
| FSQRT_RMM_S_64F
| FSQRT_DYN_S_64F
| FSGNJ_S_64F
| FSGNJN_S_64F
| FSGNJX_S_64F
| FMIN_S_64F
| FMAX_S_64F
| FCVT_RNE_W_S_64F
| FCVT_RTZ_W_S_64F
| FCVT_RDN_W_S_64F
| FCVT_RUP_W_S_64F
| FCVT_RMM_W_S_64F
| FCVT_DYN_W_S_64F
| FCVT_RNE_WU_S_64F
| FCVT_RTZ_WU_S_64F
| FCVT_RDN_WU_S_64F
| FCVT_RUP_WU_S_64F
| FCVT_RMM_WU_S_64F
| FCVT_DYN_WU_S_64F
| FMV_X_W_64F
| FEQ_S_64F
| FLT_S_64F
| FLE_S_64F
| FCLASS_S_64F
| FCVT_RNE_S_W_64F
| FCVT_RTZ_S_W_64F
| FCVT_RDN_S_W_64F
| FCVT_RUP_S_W_64F
| FCVT_RMM_S_W_64F
| FCVT_DYN_S_W_64F
| FCVT_RNE_S_WU_64F
| FCVT_RTZ_S_WU_64F
| FCVT_RDN_S_WU_64F
| FCVT_RUP_S_WU_64F
| FCVT_RMM_S_WU_64F
| FCVT_DYN_S_WU_64F
| FMV_W_X_64F
| FCVT_RNE_L_S_64F
| FCVT_RTZ_L_S_64F
| FCVT_RDN_L_S_64F
| FCVT_RUP_L_S_64F
| FCVT_RMM_L_S_64F
| FCVT_DYN_L_S_64F
| FCVT_RNE_LU_S_64F
| FCVT_RTZ_LU_S_64F
| FCVT_RDN_LU_S_64F
| FCVT_RUP_LU_S_64F
| FCVT_RMM_LU_S_64F
| FCVT_DYN_LU_S_64F
| FCVT_RNE_S_L_64F
| FCVT_RTZ_S_L_64F
| FCVT_RDN_S_L_64F
| FCVT_RUP_S_L_64F
| FCVT_RMM_S_L_64F
| FCVT_DYN_S_L_64F
| FCVT_RNE_S_LU_64F
| FCVT_RTZ_S_LU_64F
| FCVT_RDN_S_LU_64F
| FCVT_RUP_S_LU_64F
| FCVT_RMM_S_LU_64F
| FCVT_DYN_S_LU_64F
| FLD_32D
| FSD_32D
| FMADD_RNE_D_32D
| FMADD_RTZ_D_32D
| FMADD_RDN_D_32D
| FMADD_RUP_D_32D
| FMADD_RMM_D_32D
| FMADD_DYN_D_32D
| FMSUB_RNE_D_32D
| FMSUB_RTZ_D_32D
| FMSUB_RDN_D_32D
| FMSUB_RUP_D_32D
| FMSUB_RMM_D_32D
| FMSUB_DYN_D_32D
| FNMSUB_RNE_D_32D
| FNMSUB_RTZ_D_32D
| FNMSUB_RDN_D_32D
| FNMSUB_RUP_D_32D
| FNMSUB_RMM_D_32D
| FNMSUB_DYN_D_32D
| FNMADD_RNE_D_32D
| FNMADD_RTZ_D_32D
| FNMADD_RDN_D_32D
| FNMADD_RUP_D_32D
| FNMADD_RMM_D_32D
| FNMADD_DYN_D_32D
| FADD_RNE_D_32D
| FADD_RTZ_D_32D
| FADD_RDN_D_32D
| FADD_RUP_D_32D
| FADD_RMM_D_32D
| FADD_DYN_D_32D
| FSUB_RNE_D_32D
| FSUB_RTZ_D_32D
| FSUB_RDN_D_32D
| FSUB_RUP_D_32D
| FSUB_RMM_D_32D
| FSUB_DYN_D_32D
| FMUL_RNE_D_32D
| FMUL_RTZ_D_32D
| FMUL_RDN_D_32D
| FMUL_RUP_D_32D
| FMUL_RMM_D_32D
| FMUL_DYN_D_32D
| FDIV_RNE_D_32D
| FDIV_RTZ_D_32D
| FDIV_RDN_D_32D
| FDIV_RUP_D_32D
| FDIV_RMM_D_32D
| FDIV_DYN_D_32D
| FSQRT_RNE_D_32D
| FSQRT_RTZ_D_32D
| FSQRT_RDN_D_32D
| FSQRT_RUP_D_32D
| FSQRT_RMM_D_32D
| FSQRT_DYN_D_32D
| FSGNJ_D_32D
| FSGNJN_D_32D
| FSGNJX_D_32D
| FMIN_D_32D
| FMAX_D_32D
| FCVT_RNE_S_D_32D
| FCVT_RTZ_S_D_32D
| FCVT_RDN_S_D_32D
| FCVT_RUP_S_D_32D
| FCVT_RMM_S_D_32D
| FCVT_DYN_S_D_32D
| FCVT_RNE_D_S_32D
| FCVT_RTZ_D_S_32D
| FCVT_RDN_D_S_32D
| FCVT_RUP_D_S_32D
| FCVT_RMM_D_S_32D
| FCVT_DYN_D_S_32D
| FEQ_D_32D
| FLT_D_32D
| FLE_D_32D
| FCLASS_D_32D
| FCVT_RNE_W_D_32D
| FCVT_RTZ_W_D_32D
| FCVT_RDN_W_D_32D
| FCVT_RUP_W_D_32D
| FCVT_RMM_W_D_32D
| FCVT_DYN_W_D_32D
| FCVT_RNE_WU_D_32D
| FCVT_RTZ_WU_D_32D
| FCVT_RDN_WU_D_32D
| FCVT_RUP_WU_D_32D
| FCVT_RMM_WU_D_32D
| FCVT_DYN_WU_D_32D
| FCVT_RNE_D_W_32D
| FCVT_RTZ_D_W_32D
| FCVT_RDN_D_W_32D
| FCVT_RUP_D_W_32D
| FCVT_RMM_D_W_32D
| FCVT_DYN_D_W_32D
| FCVT_RNE_D_WU_32D
| FCVT_RTZ_D_WU_32D
| FCVT_RDN_D_WU_32D
| FCVT_RUP_D_WU_32D
| FCVT_RMM_D_WU_32D
| FCVT_DYN_D_WU_32D
| FLD_64D
| FSD_64D
| FMADD_RNE_D_64D
| FMADD_RTZ_D_64D
| FMADD_RDN_D_64D
| FMADD_RUP_D_64D
| FMADD_RMM_D_64D
| FMADD_DYN_D_64D
| FMSUB_RNE_D_64D
| FMSUB_RTZ_D_64D
| FMSUB_RDN_D_64D
| FMSUB_RUP_D_64D
| FMSUB_RMM_D_64D
| FMSUB_DYN_D_64D
| FNMSUB_RNE_D_64D
| FNMSUB_RTZ_D_64D
| FNMSUB_RDN_D_64D
| FNMSUB_RUP_D_64D
| FNMSUB_RMM_D_64D
| FNMSUB_DYN_D_64D
| FNMADD_RNE_D_64D
| FNMADD_RTZ_D_64D
| FNMADD_RDN_D_64D
| FNMADD_RUP_D_64D
| FNMADD_RMM_D_64D
| FNMADD_DYN_D_64D
| FADD_RNE_D_64D
| FADD_RTZ_D_64D
| FADD_RDN_D_64D
| FADD_RUP_D_64D
| FADD_RMM_D_64D
| FADD_DYN_D_64D
| FSUB_RNE_D_64D
| FSUB_RTZ_D_64D
| FSUB_RDN_D_64D
| FSUB_RUP_D_64D
| FSUB_RMM_D_64D
| FSUB_DYN_D_64D
| FMUL_RNE_D_64D
| FMUL_RTZ_D_64D
| FMUL_RDN_D_64D
| FMUL_RUP_D_64D
| FMUL_RMM_D_64D
| FMUL_DYN_D_64D
| FDIV_RNE_D_64D
| FDIV_RTZ_D_64D
| FDIV_RDN_D_64D
| FDIV_RUP_D_64D
| FDIV_RMM_D_64D
| FDIV_DYN_D_64D
| FSQRT_RNE_D_64D
| FSQRT_RTZ_D_64D
| FSQRT_RDN_D_64D
| FSQRT_RUP_D_64D
| FSQRT_RMM_D_64D
| FSQRT_DYN_D_64D
| FSGNJ_D_64D
| FSGNJN_D_64D
| FSGNJX_D_64D
| FMIN_D_64D
| FMAX_D_64D
| FCVT_RNE_S_D_64D
| FCVT_RTZ_S_D_64D
| FCVT_RDN_S_D_64D
| FCVT_RUP_S_D_64D
| FCVT_RMM_S_D_64D
| FCVT_DYN_S_D_64D
| FCVT_RNE_D_S_64D
| FCVT_RTZ_D_S_64D
| FCVT_RDN_D_S_64D
| FCVT_RUP_D_S_64D
| FCVT_RMM_D_S_64D
| FCVT_DYN_D_S_64D
| FEQ_D_64D
| FLT_D_64D
| FLE_D_64D
| FCLASS_D_64D
| FCVT_RNE_W_D_64D
| FCVT_RTZ_W_D_64D
| FCVT_RDN_W_D_64D
| FCVT_RUP_W_D_64D
| FCVT_RMM_W_D_64D
| FCVT_DYN_W_D_64D
| FCVT_RNE_WU_D_64D
| FCVT_RTZ_WU_D_64D
| FCVT_RDN_WU_D_64D
| FCVT_RUP_WU_D_64D
| FCVT_RMM_WU_D_64D
| FCVT_DYN_WU_D_64D
| FCVT_RNE_D_W_64D
| FCVT_RTZ_D_W_64D
| FCVT_RDN_D_W_64D
| FCVT_RUP_D_W_64D
| FCVT_RMM_D_W_64D
| FCVT_DYN_D_W_64D
| FCVT_RNE_D_WU_64D
| FCVT_RTZ_D_WU_64D
| FCVT_RDN_D_WU_64D
| FCVT_RUP_D_WU_64D
| FCVT_RMM_D_WU_64D
| FCVT_DYN_D_WU_64D
| FCVT_RNE_L_D_64D
| FCVT_RTZ_L_D_64D
| FCVT_RDN_L_D_64D
| FCVT_RUP_L_D_64D
| FCVT_RMM_L_D_64D
| FCVT_DYN_L_D_64D
| FCVT_RNE_LU_D_64D
| FCVT_RTZ_LU_D_64D
| FCVT_RDN_LU_D_64D
| FCVT_RUP_LU_D_64D
| FCVT_RMM_LU_D_64D
| FCVT_DYN_LU_D_64D
| FMV_X_D_64D
| FCVT_RNE_D_L_64D
| FCVT_RTZ_D_L_64D
| FCVT_RDN_D_L_64D
| FCVT_RUP_D_L_64D
| FCVT_RMM_D_L_64D
| FCVT_DYN_D_L_64D
| FCVT_RNE_D_LU_64D
| FCVT_RTZ_D_LU_64D
| FCVT_RDN_D_LU_64D
| FCVT_RUP_D_LU_64D
| FCVT_RMM_D_LU_64D
| FCVT_DYN_D_LU_64D
| FMV_D_X_64D
| FLQ_32Q
| FSQ_32Q
| FMADD_RNE_Q_32Q
| FMADD_RTZ_Q_32Q
| FMADD_RDN_Q_32Q
| FMADD_RUP_Q_32Q
| FMADD_RMM_Q_32Q
| FMADD_DYN_Q_32Q
| FMSUB_RNE_Q_32Q
| FMSUB_RTZ_Q_32Q
| FMSUB_RDN_Q_32Q
| FMSUB_RUP_Q_32Q
| FMSUB_RMM_Q_32Q
| FMSUB_DYN_Q_32Q
| FNMSUB_RNE_Q_32Q
| FNMSUB_RTZ_Q_32Q
| FNMSUB_RDN_Q_32Q
| FNMSUB_RUP_Q_32Q
| FNMSUB_RMM_Q_32Q
| FNMSUB_DYN_Q_32Q
| FNMADD_RNE_Q_32Q
| FNMADD_RTZ_Q_32Q
| FNMADD_RDN_Q_32Q
| FNMADD_RUP_Q_32Q
| FNMADD_RMM_Q_32Q
| FNMADD_DYN_Q_32Q
| FADD_RNE_Q_32Q
| FADD_RTZ_Q_32Q
| FADD_RDN_Q_32Q
| FADD_RUP_Q_32Q
| FADD_RMM_Q_32Q
| FADD_DYN_Q_32Q
| FSUB_RNE_Q_32Q
| FSUB_RTZ_Q_32Q
| FSUB_RDN_Q_32Q
| FSUB_RUP_Q_32Q
| FSUB_RMM_Q_32Q
| FSUB_DYN_Q_32Q
| FMUL_RNE_Q_32Q
| FMUL_RTZ_Q_32Q
| FMUL_RDN_Q_32Q
| FMUL_RUP_Q_32Q
| FMUL_RMM_Q_32Q
| FMUL_DYN_Q_32Q
| FDIV_RNE_Q_32Q
| FDIV_RTZ_Q_32Q
| FDIV_RDN_Q_32Q
| FDIV_RUP_Q_32Q
| FDIV_RMM_Q_32Q
| FDIV_DYN_Q_32Q
| FSQRT_RNE_Q_32Q
| FSQRT_RTZ_Q_32Q
| FSQRT_RDN_Q_32Q
| FSQRT_RUP_Q_32Q
| FSQRT_RMM_Q_32Q
| FSQRT_DYN_Q_32Q
| FSGNJ_Q_32Q
| FSGNJN_Q_32Q
| FSGNJX_Q_32Q
| FMIN_Q_32Q
| FMAX_Q_32Q
| FCVT_RNE_S_Q_32Q
| FCVT_RTZ_S_Q_32Q
| FCVT_RDN_S_Q_32Q
| FCVT_RUP_S_Q_32Q
| FCVT_RMM_S_Q_32Q
| FCVT_DYN_S_Q_32Q
| FCVT_RNE_Q_S_32Q
| FCVT_RTZ_Q_S_32Q
| FCVT_RDN_Q_S_32Q
| FCVT_RUP_Q_S_32Q
| FCVT_RMM_Q_S_32Q
| FCVT_DYN_Q_S_32Q
| FCVT_RNE_D_Q_32Q
| FCVT_RTZ_D_Q_32Q
| FCVT_RDN_D_Q_32Q
| FCVT_RUP_D_Q_32Q
| FCVT_RMM_D_Q_32Q
| FCVT_DYN_D_Q_32Q
| FCVT_RNE_Q_D_32Q
| FCVT_RTZ_Q_D_32Q
| FCVT_RDN_Q_D_32Q
| FCVT_RUP_Q_D_32Q
| FCVT_RMM_Q_D_32Q
| FCVT_DYN_Q_D_32Q
| FEQ_Q_32Q
| FLT_Q_32Q
| FLE_Q_32Q
| FCLASS_Q_32Q
| FCVT_RNE_W_Q_32Q
| FCVT_RTZ_W_Q_32Q
| FCVT_RDN_W_Q_32Q
| FCVT_RUP_W_Q_32Q
| FCVT_RMM_W_Q_32Q
| FCVT_DYN_W_Q_32Q
| FCVT_RNE_WU_Q_32Q
| FCVT_RTZ_WU_Q_32Q
| FCVT_RDN_WU_Q_32Q
| FCVT_RUP_WU_Q_32Q
| FCVT_RMM_WU_Q_32Q
| FCVT_DYN_WU_Q_32Q
| FCVT_RNE_Q_W_32Q
| FCVT_RTZ_Q_W_32Q
| FCVT_RDN_Q_W_32Q
| FCVT_RUP_Q_W_32Q
| FCVT_RMM_Q_W_32Q
| FCVT_DYN_Q_W_32Q
| FCVT_RNE_Q_WU_32Q
| FCVT_RTZ_Q_WU_32Q
| FCVT_RDN_Q_WU_32Q
| FCVT_RUP_Q_WU_32Q
| FCVT_RMM_Q_WU_32Q
| FCVT_DYN_Q_WU_32Q
| FLQ_64Q
| FSQ_64Q
| FMADD_RNE_Q_64Q
| FMADD_RTZ_Q_64Q
| FMADD_RDN_Q_64Q
| FMADD_RUP_Q_64Q
| FMADD_RMM_Q_64Q
| FMADD_DYN_Q_64Q
| FMSUB_RNE_Q_64Q
| FMSUB_RTZ_Q_64Q
| FMSUB_RDN_Q_64Q
| FMSUB_RUP_Q_64Q
| FMSUB_RMM_Q_64Q
| FMSUB_DYN_Q_64Q
| FNMSUB_RNE_Q_64Q
| FNMSUB_RTZ_Q_64Q
| FNMSUB_RDN_Q_64Q
| FNMSUB_RUP_Q_64Q
| FNMSUB_RMM_Q_64Q
| FNMSUB_DYN_Q_64Q
| FNMADD_RNE_Q_64Q
| FNMADD_RTZ_Q_64Q
| FNMADD_RDN_Q_64Q
| FNMADD_RUP_Q_64Q
| FNMADD_RMM_Q_64Q
| FNMADD_DYN_Q_64Q
| FADD_RNE_Q_64Q
| FADD_RTZ_Q_64Q
| FADD_RDN_Q_64Q
| FADD_RUP_Q_64Q
| FADD_RMM_Q_64Q
| FADD_DYN_Q_64Q
| FSUB_RNE_Q_64Q
| FSUB_RTZ_Q_64Q
| FSUB_RDN_Q_64Q
| FSUB_RUP_Q_64Q
| FSUB_RMM_Q_64Q
| FSUB_DYN_Q_64Q
| FMUL_RNE_Q_64Q
| FMUL_RTZ_Q_64Q
| FMUL_RDN_Q_64Q
| FMUL_RUP_Q_64Q
| FMUL_RMM_Q_64Q
| FMUL_DYN_Q_64Q
| FDIV_RNE_Q_64Q
| FDIV_RTZ_Q_64Q
| FDIV_RDN_Q_64Q
| FDIV_RUP_Q_64Q
| FDIV_RMM_Q_64Q
| FDIV_DYN_Q_64Q
| FSQRT_RNE_Q_64Q
| FSQRT_RTZ_Q_64Q
| FSQRT_RDN_Q_64Q
| FSQRT_RUP_Q_64Q
| FSQRT_RMM_Q_64Q
| FSQRT_DYN_Q_64Q
| FSGNJ_Q_64Q
| FSGNJN_Q_64Q
| FSGNJX_Q_64Q
| FMIN_Q_64Q
| FMAX_Q_64Q
| FCVT_RNE_S_Q_64Q
| FCVT_RTZ_S_Q_64Q
| FCVT_RDN_S_Q_64Q
| FCVT_RUP_S_Q_64Q
| FCVT_RMM_S_Q_64Q
| FCVT_DYN_S_Q_64Q
| FCVT_RNE_Q_S_64Q
| FCVT_RTZ_Q_S_64Q
| FCVT_RDN_Q_S_64Q
| FCVT_RUP_Q_S_64Q
| FCVT_RMM_Q_S_64Q
| FCVT_DYN_Q_S_64Q
| FCVT_RNE_D_Q_64Q
| FCVT_RTZ_D_Q_64Q
| FCVT_RDN_D_Q_64Q
| FCVT_RUP_D_Q_64Q
| FCVT_RMM_D_Q_64Q
| FCVT_DYN_D_Q_64Q
| FCVT_RNE_Q_D_64Q
| FCVT_RTZ_Q_D_64Q
| FCVT_RDN_Q_D_64Q
| FCVT_RUP_Q_D_64Q
| FCVT_RMM_Q_D_64Q
| FCVT_DYN_Q_D_64Q
| FEQ_Q_64Q
| FLT_Q_64Q
| FLE_Q_64Q
| FCLASS_Q_64Q
| FCVT_RNE_W_Q_64Q
| FCVT_RTZ_W_Q_64Q
| FCVT_RDN_W_Q_64Q
| FCVT_RUP_W_Q_64Q
| FCVT_RMM_W_Q_64Q
| FCVT_DYN_W_Q_64Q
| FCVT_RNE_WU_Q_64Q
| FCVT_RTZ_WU_Q_64Q
| FCVT_RDN_WU_Q_64Q
| FCVT_RUP_WU_Q_64Q
| FCVT_RMM_WU_Q_64Q
| FCVT_DYN_WU_Q_64Q
| FCVT_RNE_Q_W_64Q
| FCVT_RTZ_Q_W_64Q
| FCVT_RDN_Q_W_64Q
| FCVT_RUP_Q_W_64Q
| FCVT_RMM_Q_W_64Q
| FCVT_DYN_Q_W_64Q
| FCVT_RNE_Q_WU_64Q
| FCVT_RTZ_Q_WU_64Q
| FCVT_RDN_Q_WU_64Q
| FCVT_RUP_Q_WU_64Q
| FCVT_RMM_Q_WU_64Q
| FCVT_DYN_Q_WU_64Q
| FCVT_RNE_L_Q_64Q
| FCVT_RTZ_L_Q_64Q
| FCVT_RDN_L_Q_64Q
| FCVT_RUP_L_Q_64Q
| FCVT_RMM_L_Q_64Q
| FCVT_DYN_L_Q_64Q
| FCVT_RNE_LU_Q_64Q
| FCVT_RTZ_LU_Q_64Q
| FCVT_RDN_LU_Q_64Q
| FCVT_RUP_LU_Q_64Q
| FCVT_RMM_LU_Q_64Q
| FCVT_DYN_LU_Q_64Q
| FCVT_RNE_Q_L_64Q
| FCVT_RTZ_Q_L_64Q
| FCVT_RDN_Q_L_64Q
| FCVT_RUP_Q_L_64Q
| FCVT_RMM_Q_L_64Q
| FCVT_DYN_Q_L_64Q
| FCVT_RNE_Q_LU_64Q
| FCVT_RTZ_Q_LU_64Q
| FCVT_RDN_Q_LU_64Q
| FCVT_RUP_Q_LU_64Q
| FCVT_RMM_Q_LU_64Q
| FCVT_DYN_Q_LU_64Q

type i_type =
| RType
| R4Type
| IType
| SType
| BType
| UType
| JType

type i_field =
| Opcode
| Fct2
| Fct3
| Fct7
| Rs1
| Rs2
| Rs3
| Rd
| ImmI
| ImmS
| ImmB
| ImmU
| ImmJ

val get_i_field_name : i_field -> char list

val has_opcode : i_type -> bool

val has_fct2 : i_type -> bool

val has_fct3 : i_type -> bool

val has_fct7 : i_type -> bool

val has_rs1 : i_type -> bool

val has_rs2 : i_type -> bool

val has_rs3 : i_type -> bool

val has_rd : i_type -> bool

val has_immI : i_type -> bool

val has_immS : i_type -> bool

val has_immB : i_type -> bool

val has_immU : i_type -> bool

val has_immJ : i_type -> bool

type subfield_properties = { first_bit : int; subfield_length : int }

type i_field_properties = { is_sign_extended : bool; shift : int;
                            i_field_subfields : subfield_properties list }

val get_i_field_properties : i_field -> i_field_properties

val rV32I_instructions : instruction list

val rV64I_instructions : instruction list

val rV32Zifencei_instructions : instruction list

val rV64Zifencei_instructions : instruction list

val rV32Zicsr_instructions : instruction list

val rV64Zicsr_instructions : instruction list

val rV32M_instructions : instruction list

val rV64M_instructions : instruction list

val rV32A_instructions : instruction list

val rV64A_instructions : instruction list

val rV32F_instructions : instruction list

val rV64F_instructions : instruction list

val rV32D_instructions : instruction list

val rV64D_instructions : instruction list

val rV32Q_instructions : instruction list

val rV64Q_instructions : instruction list

val extension_instructions : base_standard -> extension -> instruction list

val iSA_instructions_set : iSA -> instruction list

type opcode_name =
| Opc_OP
| Opc_JALR
| Opc_LOAD
| Opc_OP_IMM
| Opc_MISC_MEM
| Opc_STORE
| Opc_BRANCH
| Opc_LUI
| Opc_AUIPC
| Opc_JAL
| Opc_SYSTEM
| Opc_OP_32
| Opc_OP_IMM_32
| Opc_AMO
| Opc_OP_FP
| Opc_MADD
| Opc_MSUB
| Opc_NMSUB
| Opc_NMADD
| Opc_LOAD_FP
| Opc_STORE_FP

val opcode_name_beq : opcode_name -> opcode_name -> bool

val opcode_bin :
  opcode_name -> (bool, (bool, (bool, (bool, (bool, (bool, (bool, __)
  vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
  vect_cons_t) vect_cons_t

val instruction_opcode : instruction -> opcode_name

val get_opcode_i_type : opcode_name -> i_type

val get_instruction_i_type : instruction -> i_type

type fct2_type =
| Fct2_00
| Fct2_01
| Fct2_11

val fct2_bin : fct2_type -> (bool, (bool, __) vect_cons_t) vect_cons_t

val fct2_type_beq : fct2_type -> fct2_type -> bool

val instruction_fct2 : instruction -> fct2_type

type fct3_type =
| Fct3_000
| Fct3_001
| Fct3_010
| Fct3_011
| Fct3_100
| Fct3_101
| Fct3_110
| Fct3_111

val fct3_type_beq : fct3_type -> fct3_type -> bool

val fct3_bin :
  fct3_type -> (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t

val instruction_fct3 : instruction -> fct3_type

type fct7_type =
| Fct7_0000000
| Fct7_0000001
| Fct7_0000010
| Fct7_0000011
| Fct7_0000100
| Fct7_0000101
| Fct7_0000110
| Fct7_0000111
| Fct7_0001000
| Fct7_0001001
| Fct7_0001010
| Fct7_0001011
| Fct7_0001100
| Fct7_0001101
| Fct7_0001110
| Fct7_0001111
| Fct7_0010000
| Fct7_0010001
| Fct7_0010010
| Fct7_0010011
| Fct7_0010100
| Fct7_0010101
| Fct7_0010111
| Fct7_0100000
| Fct7_0100001
| Fct7_0100010
| Fct7_0100011
| Fct7_0101100
| Fct7_0101101
| Fct7_0101111
| Fct7_0110000
| Fct7_0110001
| Fct7_0110010
| Fct7_0110011
| Fct7_1000000
| Fct7_1000001
| Fct7_1000010
| Fct7_1000011
| Fct7_1010000
| Fct7_1010001
| Fct7_1010010
| Fct7_1010011
| Fct7_1100000
| Fct7_1100001
| Fct7_1100010
| Fct7_1100011
| Fct7_1101000
| Fct7_1101001
| Fct7_1101011
| Fct7_1110000
| Fct7_1110001
| Fct7_1110010
| Fct7_1110011
| Fct7_1111000
| Fct7_1111001
| Fct7_1111011

val fct7_type_beq : fct7_type -> fct7_type -> bool

val fct7_bin :
  fct7_type -> (bool, (bool, (bool, (bool, (bool, (bool, (bool, __)
  vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
  vect_cons_t) vect_cons_t

val instruction_fct7 : instruction -> fct7_type

type present_i_types = { rType_present : bool; r4Type_present : bool;
                         iType_present : bool; sType_present : bool;
                         bType_present : bool; uType_present : bool;
                         jType_present : bool }

type present_i_fields = { opcode_present : bool; fct2_present : bool;
                          fct3_present : bool; fct7_present : bool;
                          rs1_present : bool; rs2_present : bool;
                          rs3_present : bool; rd_present : bool;
                          immI_present : bool; immS_present : bool;
                          immB_present : bool; immU_present : bool;
                          immJ_present : bool }

type present_opcodes = { opc_OP_present : bool; opc_JALR_present : bool;
                         opc_LOAD_present : bool; opc_OP_IMM_present : 
                         bool; opc_MISC_MEM_present : bool;
                         opc_STORE_present : bool; opc_BRANCH_present : 
                         bool; opc_LUI_present : bool;
                         opc_AUIPC_present : bool; opc_JAL_present : 
                         bool; opc_SYSTEM_present : bool;
                         opc_OP_32_present : bool;
                         opc_OP_IMM_32_present : bool;
                         opc_AMO_present : bool; opc_OP_FP_present : 
                         bool; opc_MADD_present : bool;
                         opc_MSUB_present : bool; opc_NMSUB_present : 
                         bool; opc_NMADD_present : bool;
                         opc_LOAD_FP_present : bool;
                         opc_STORE_FP_present : bool }

val get_present_i_types_from_instructions :
  instruction list -> present_i_types

val check_i_type_presence : present_i_types -> i_type -> i_type option

val get_i_types_from_present_i_types : present_i_types -> i_type list

val get_present_i_fields_from_i_type : i_type -> present_i_fields

val merge_present_i_fields :
  present_i_fields -> present_i_fields -> present_i_fields

val get_present_i_fields_from_i_types : i_type list -> present_i_fields

val check_i_field_presence : present_i_fields -> i_field -> i_field option

val get_i_fields_list_from_present_i_fields : present_i_fields -> i_field list

val get_i_fields_list_from_instructions : instruction list -> i_field list

val get_present_opcodes_from_instructions :
  instruction list -> present_opcodes

val check_opcode_presence :
  present_opcodes -> opcode_name -> opcode_name option

val get_opcodes_from_present_opcodes : present_opcodes -> opcode_name list

val get_opcodes_from_instructions_list : instruction list -> opcode_name list

val get_rs1_users : instruction list -> instruction list

val get_rs2_users : instruction list -> instruction list

val get_rd_users : instruction list -> instruction list

val optional_prepend : ('a1 -> bool) -> 'a1 -> 'a1 list sig0 -> 'a1 list sig0

val custom_filter : ('a1 -> bool) -> 'a1 list -> 'a1 list sig0

val to_list_of_dependents : ('a1 -> bool) -> 'a1 list sig0 -> 'a1 sig0 list

val remove_dups : 'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 list

val get_fcts3 : opcode_name -> instruction list -> fct3_type list

val get_fcts2 : opcode_name -> fct3_type -> instruction list -> fct2_type list

val get_fcts7 : opcode_name -> fct3_type -> instruction list -> fct7_type list

val get_imm_fields_from_instructions : instruction list -> i_field list

val get_i_field_information_quantity : i_field -> int

val get_i_field_base_information_quantity : i_field -> int

val get_i_fields_formatted_for_struct :
  instruction list -> (char list * type0) list

val get_inst_fields_struct_from_ISA : iSA -> type0 struct_sig'

val isa : iSA

val instructions : instruction list

val imm_type : enum_sig

val decoded_sig : type0 struct_sig'

val inst_field : type0 struct_sig'

val getFields :
  'a1 finiteType -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __)
  uaction) internalFunction

val isLegalInstruction :
  'a1 finiteType -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __)
  uaction) internalFunction

val getImmediateType :
  'a1 finiteType -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __)
  uaction) internalFunction

val usesRS1 :
  (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __) uaction)
  internalFunction

val usesRS2 :
  (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __) uaction)
  internalFunction

val usesRD :
  (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __) uaction)
  internalFunction

val decode_fun :
  'a1 finiteType -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __)
  uaction) internalFunction

val getImmediate :
  'a1 finiteType -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __)
  uaction) internalFunction

val alu32 :
  (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __) uaction)
  internalFunction

val execALU32 :
  'a1 finiteType -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __)
  uaction) internalFunction

val control_result : type0 struct_sig'

val execControl32 :
  'a1 finiteType -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __)
  uaction) internalFunction

type rv_rules_t =
| Fetch
| Decode
| Execute
| Writeback
| WaitImem
| Imem
| Dmem
| Tick
| UpdateOnOff
| EndExecution

val rv_external : rv_rules_t -> bool

module type Core =
 sig
  type _reg_t

  type _ext_fn_t

  val coq_R : _reg_t -> type0

  val coq_Sigma : _ext_fn_t -> externalSignature

  val r : _reg_t -> type_denote

  val rv_rules :
    rv_rules_t -> (pos_t, var_t, fn_name_t, _reg_t, _ext_fn_t) rule

  val coq_FiniteType_reg_t : _reg_t finiteType

  val coq_Show_reg_t : _reg_t show

  val coq_Show_ext_fn_t : _ext_fn_t show

  val rv_ext_fn_sim_specs : _ext_fn_t -> ext_fn_sim_spec

  val rv_ext_fn_rtl_specs : _ext_fn_t -> ext_fn_rtl_spec
 end

val rv_schedule : (pos_t, rv_rules_t) scheduler

module Package :
 functor (C:Core) ->
 sig
  val circuits : (rv_rules_t, C._reg_t, C._ext_fn_t) register_update_circuitry

  val koika_package :
    (pos_t, var_t, fn_name_t, rv_rules_t, C._reg_t, C._ext_fn_t)
    koika_package_t

  val package : interop_package_t
 end

module RVIParams :
 sig
  val coq_NREGS : int

  val coq_HAS_SHADOW_STACK : bool
 end

module RV32I :
 sig
  module ShadowStack :
   sig
    val capacity : int

    type _reg_t = ShadowStackF._reg_t =
    | Coq_size
    | Coq_stack of index

    val _reg_t_rect : 'a1 -> (index -> 'a1) -> _reg_t -> 'a1

    val _reg_t_rec : 'a1 -> (index -> 'a1) -> _reg_t -> 'a1

    type reg_t = _reg_t

    val coq_R : _reg_t -> type0

    val r : _reg_t -> type_denote

    val read_vect_sequential :
      char list -> (pos_t, var_t, fn_name_t, reg_t, __) uaction

    val write0_stack :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val push :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val pop :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val coq_Show_reg_t : reg_t show

    val coq_FiniteType_reg_t : reg_t finiteType
   end

  val mem_req : type0 struct_sig'

  val mem_resp : type0 struct_sig'

  val fetch_bookkeeping : type0 struct_sig'

  val decode_bookkeeping : type0 struct_sig'

  val execute_bookkeeping : type0 struct_sig'

  module FifoMemReq :
   sig
    val coq_T : type0
   end

  module MemReq :
   sig
    type reg_t =
    | Coq_data0
    | Coq_valid0

    val reg_t_rect : 'a1 -> 'a1 -> reg_t -> 'a1

    val reg_t_rec : 'a1 -> 'a1 -> reg_t -> 'a1

    val coq_R : reg_t -> type0

    val r : reg_t -> type_denote

    val name_reg : reg_t -> char list

    val can_enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val can_deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val peek :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val coq_FiniteType_reg_t : reg_t finiteType
   end

  module FifoMemResp :
   sig
    val coq_T : type0
   end

  module MemResp :
   sig
    type reg_t =
    | Coq_data0
    | Coq_valid0

    val reg_t_rect : 'a1 -> 'a1 -> reg_t -> 'a1

    val reg_t_rec : 'a1 -> 'a1 -> reg_t -> 'a1

    val coq_R : reg_t -> type0

    val r : reg_t -> type_denote

    val name_reg : reg_t -> char list

    val can_enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val can_deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val peek :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val coq_FiniteType_reg_t : reg_t finiteType
   end

  module FifoUART :
   sig
    val coq_T : type0
   end

  module UARTReq :
   sig
    type reg_t =
    | Coq_data0
    | Coq_valid0

    val reg_t_rect : 'a1 -> 'a1 -> reg_t -> 'a1

    val reg_t_rec : 'a1 -> 'a1 -> reg_t -> 'a1

    val coq_R : reg_t -> type0

    val r : reg_t -> type_denote

    val name_reg : reg_t -> char list

    val can_enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val can_deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val peek :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val coq_FiniteType_reg_t : reg_t finiteType
   end

  module UARTResp :
   sig
    type reg_t =
    | Coq_data0
    | Coq_valid0

    val reg_t_rect : 'a1 -> 'a1 -> reg_t -> 'a1

    val reg_t_rec : 'a1 -> 'a1 -> reg_t -> 'a1

    val coq_R : reg_t -> type0

    val r : reg_t -> type_denote

    val name_reg : reg_t -> char list

    val can_enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val can_deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val peek :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val coq_FiniteType_reg_t : reg_t finiteType
   end

  module FifoFetch :
   sig
    val coq_T : type0
   end

  module Coq_fromFetch :
   sig
    type reg_t =
    | Coq_data0
    | Coq_valid0

    val reg_t_rect : 'a1 -> 'a1 -> reg_t -> 'a1

    val reg_t_rec : 'a1 -> 'a1 -> reg_t -> 'a1

    val coq_R : reg_t -> type0

    val r : reg_t -> type_denote

    val name_reg : reg_t -> char list

    val can_enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val can_deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val peek :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val coq_FiniteType_reg_t : reg_t finiteType
   end

  module Coq_waitFromFetch :
   sig
    type reg_t =
    | Coq_data0
    | Coq_valid0

    val reg_t_rect : 'a1 -> 'a1 -> reg_t -> 'a1

    val reg_t_rec : 'a1 -> 'a1 -> reg_t -> 'a1

    val coq_R : reg_t -> type0

    val r : reg_t -> type_denote

    val name_reg : reg_t -> char list

    val can_enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val can_deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val peek :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val coq_FiniteType_reg_t : reg_t finiteType
   end

  module FifoDecode :
   sig
    val coq_T : type0
   end

  module Coq_fromDecode :
   sig
    type reg_t =
    | Coq_data0
    | Coq_valid0

    val reg_t_rect : 'a1 -> 'a1 -> reg_t -> 'a1

    val reg_t_rec : 'a1 -> 'a1 -> reg_t -> 'a1

    val coq_R : reg_t -> type0

    val r : reg_t -> type_denote

    val name_reg : reg_t -> char list

    val can_enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val can_deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val peek :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val coq_FiniteType_reg_t : reg_t finiteType
   end

  module FifoExecute :
   sig
    val coq_T : type0
   end

  module Coq_fromExecute :
   sig
    type reg_t =
    | Coq_data0
    | Coq_valid0

    val reg_t_rect : 'a1 -> 'a1 -> reg_t -> 'a1

    val reg_t_rec : 'a1 -> 'a1 -> reg_t -> 'a1

    val coq_R : reg_t -> type0

    val r : reg_t -> type_denote

    val name_reg : reg_t -> char list

    val can_enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val can_deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val peek :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val coq_FiniteType_reg_t : reg_t finiteType
   end

  module RfParams :
   sig
    val idx_sz : int

    val coq_T : type0

    val init :
      (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
      (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
      (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
      (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t

    val read_style : var_t switch_style

    val write_style : var_t switch_style
   end

  module Rf :
   sig
    val sz : int

    type reg_t =
    | Coq_rData of index

    val reg_t_rect : (index -> 'a1) -> reg_t -> 'a1

    val reg_t_rec : (index -> 'a1) -> reg_t -> 'a1

    val finite_rf_reg : reg_t finiteType

    val coq_R : reg_t -> type0

    val r : reg_t -> type_denote

    val name_reg : reg_t -> char list

    val read_0 :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val write_0 :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val read_1 :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val write_1 :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction
   end

  module ScoreboardParams :
   sig
    val idx_sz : int

    val maxScore : int
   end

  module Scoreboard :
   sig
    val sz : int

    val logScore : int

    module RfParams :
     sig
      val idx_sz : int

      val coq_T : type0

      val init : bool vect

      val read_style : var_t switch_style

      val write_style : var_t switch_style
     end

    module Rf :
     sig
      val sz : int

      type reg_t =
      | Coq_rData of index

      val reg_t_rect : (index -> 'a1) -> reg_t -> 'a1

      val reg_t_rec : (index -> 'a1) -> reg_t -> 'a1

      val finite_rf_reg : reg_t finiteType

      val coq_R : reg_t -> type0

      val r : reg_t -> type_denote

      val name_reg : reg_t -> char list

      val read_0 :
        (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
        internalFunction

      val write_0 :
        (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
        internalFunction

      val read_1 :
        (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
        internalFunction

      val write_1 :
        (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
        internalFunction
     end

    type reg_t =
    | Scores of Rf.reg_t

    val reg_t_rect : (Rf.reg_t -> 'a1) -> reg_t -> 'a1

    val reg_t_rec : (Rf.reg_t -> 'a1) -> reg_t -> 'a1

    val coq_R : reg_t -> type0

    val r : reg_t -> type_denote

    val name_reg : reg_t -> char list

    val sat_incr :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val sat_decr :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val finite_rf_reg : Rf.reg_t finiteType

    val finite_reg : reg_t finiteType

    val insert :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val remove :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction

    val search :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction
   end

  type reg_t =
  | Coq_toIMem of MemReq.reg_t
  | Coq_fromIMem of MemResp.reg_t
  | Coq_toDMem of MemReq.reg_t
  | Coq_fromDMem of MemResp.reg_t
  | Coq_f2d of Coq_fromFetch.reg_t
  | Coq_f2dprim of Coq_waitFromFetch.reg_t
  | Coq_d2e of Coq_fromDecode.reg_t
  | Coq_e2w of Coq_fromExecute.reg_t
  | Coq_rf of Rf.reg_t
  | Coq_stack of ShadowStack.reg_t
  | Coq_scoreboard of Scoreboard.reg_t
  | Coq_cycle_count
  | Coq_instr_count
  | Coq_pc
  | Coq_epoch
  | Coq_debug
  | Coq_on_off
  | Coq_halt

  val reg_t_rect :
    (MemReq.reg_t -> 'a1) -> (MemResp.reg_t -> 'a1) -> (MemReq.reg_t -> 'a1)
    -> (MemResp.reg_t -> 'a1) -> (Coq_fromFetch.reg_t -> 'a1) ->
    (Coq_waitFromFetch.reg_t -> 'a1) -> (Coq_fromDecode.reg_t -> 'a1) ->
    (Coq_fromExecute.reg_t -> 'a1) -> (Rf.reg_t -> 'a1) -> (ShadowStack.reg_t
    -> 'a1) -> (Scoreboard.reg_t -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> reg_t -> 'a1

  val reg_t_rec :
    (MemReq.reg_t -> 'a1) -> (MemResp.reg_t -> 'a1) -> (MemReq.reg_t -> 'a1)
    -> (MemResp.reg_t -> 'a1) -> (Coq_fromFetch.reg_t -> 'a1) ->
    (Coq_waitFromFetch.reg_t -> 'a1) -> (Coq_fromDecode.reg_t -> 'a1) ->
    (Coq_fromExecute.reg_t -> 'a1) -> (Rf.reg_t -> 'a1) -> (ShadowStack.reg_t
    -> 'a1) -> (Scoreboard.reg_t -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> reg_t -> 'a1

  val coq_R : reg_t -> type0

  val r : reg_t -> type_denote

  type memory =
  | Coq_imem
  | Coq_dmem

  val memory_rect : 'a1 -> 'a1 -> memory -> 'a1

  val memory_rec : 'a1 -> 'a1 -> memory -> 'a1

  type ext_fn_t =
  | Coq_ext_mem of memory
  | Coq_ext_uart_read
  | Coq_ext_uart_write
  | Coq_ext_led
  | Coq_ext_host_id
  | Coq_ext_finish

  val ext_fn_t_rect :
    (memory -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> ext_fn_t -> 'a1

  val ext_fn_t_rec :
    (memory -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> ext_fn_t -> 'a1

  val mem_input : type0 struct_sig'

  val mem_output : type0 struct_sig'

  val uart_input : type0

  val uart_output : type0

  val led_input : type0

  val finish_input : type0

  val host_id : enum_sig

  val coq_Sigma : ext_fn_t -> type0 _Sig

  val update_on_off : (pos_t, var_t, fn_name_t, reg_t, ext_fn_t) uaction

  val end_execution : (pos_t, var_t, fn_name_t, reg_t, ext_fn_t) uaction

  val fetch : (pos_t, var_t, fn_name_t, reg_t, ext_fn_t) uaction

  val wait_imem : (pos_t, var_t, fn_name_t, reg_t, ext_fn_t) uaction

  val sliceReg :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val decode :
    reg_t finiteType -> ShadowStack.reg_t finiteType -> (pos_t, var_t,
    fn_name_t, reg_t, ext_fn_t) uaction

  val isMemoryInst :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val isControlInst :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val isJALXInst :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
    internalFunction

  val execute_1 :
    reg_t finiteType -> ShadowStack.reg_t finiteType -> (pos_t, var_t,
    fn_name_t, reg_t, ext_fn_t) uaction

  val execute :
    reg_t finiteType -> ShadowStack.reg_t finiteType -> (pos_t, var_t,
    fn_name_t, reg_t, ext_fn_t) uaction

  val writeback :
    reg_t finiteType -> ShadowStack.reg_t finiteType -> (pos_t, var_t,
    fn_name_t, reg_t, ext_fn_t) uaction

  val coq_MMIO_UART_ADDRESS :
    (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
    (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
    (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
    (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t

  val coq_MMIO_LED_ADDRESS :
    (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
    (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
    (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
    (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t

  val coq_MMIO_EXIT_ADDRESS :
    (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
    (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
    (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
    (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t

  val coq_MMIO_HOST_ID_ADDRESS :
    (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
    (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
    (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
    (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t

  val memoryBus :
    memory -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, ext_fn_t)
    uaction) internalFunction

  val mem :
    memory -> reg_t finiteType -> ShadowStack.reg_t finiteType -> (pos_t,
    var_t, fn_name_t, reg_t, ext_fn_t) uaction

  val tick : (pos_t, var_t, fn_name_t, reg_t, ext_fn_t) uaction

  val coq_Show_reg_t : reg_t show

  val coq_Show_ext_fn_t : ext_fn_t show

  val rv_ext_fn_sim_specs : ext_fn_t -> ext_fn_sim_spec

  val rv_ext_fn_rtl_specs : ext_fn_t -> ext_fn_rtl_spec

  val coq_FiniteType_rf : Rf.reg_t finiteType

  val coq_FiniteType_scoreboard_rf : Scoreboard.Rf.reg_t finiteType

  val coq_FiniteType_scoreboard : Scoreboard.reg_t finiteType

  val coq_FiniteType_reg_t : reg_t finiteType

  val coq_FiniteType_reg_t2 : reg_t finiteType

  type _reg_t = reg_t

  type _ext_fn_t = ext_fn_t

  val rv_urules :
    rv_rules_t -> (pos_t, var_t, fn_name_t, reg_t, ext_fn_t) uaction

  val rv_rules : rv_rules_t -> (pos_t, var_t, fn_name_t, reg_t, ext_fn_t) rule
 end

module RV32IPackage :
 sig
  val circuits :
    (rv_rules_t, RV32I._reg_t, RV32I._ext_fn_t) register_update_circuitry

  val koika_package :
    (pos_t, var_t, fn_name_t, rv_rules_t, RV32I._reg_t, RV32I._ext_fn_t)
    koika_package_t

  val package : interop_package_t
 end

val prog : unit
