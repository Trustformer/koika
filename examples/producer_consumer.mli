
type __ = Obj.t

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

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

  val compare : int -> int -> comparison

  val max : int -> int -> int

  val pow : int -> int -> int

  val log2_iter : int -> int -> int -> int -> int

  val log2 : int -> int

  val log2_up : int -> int
 end

module N :
 sig
  val zero : int

  val one : int
 end

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list

val skipn : int -> 'a1 list -> 'a1 list

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

type ('a, 'b) vect_cons_t = { vhd : 'a; vtl : 'b }

type 't vect = __

val vect_hd : int -> ('a1, __) vect_cons_t -> 'a1

val vect_tl : int -> ('a1, __) vect_cons_t -> 'a1 vect

val vect_cons : int -> 'a1 -> 'a1 vect -> ('a1, __) vect_cons_t

val vect_const : int -> 'a1 -> 'a1 vect

val vect_nth : int -> 'a1 vect -> index -> 'a1

val vect_map : int -> ('a1 -> 'a2) -> 'a1 vect -> 'a2 vect

val vect_find_index : int -> ('a1 -> bool) -> 'a1 vect -> index option

val vect_index : int -> 'a1 eqDec -> 'a1 -> 'a1 vect -> index option

val eqDec_vect_nil : 'a1 eqDec -> __ eqDec

val eqDec_vect_cons : 'a1 eqDec -> 'a2 eqDec -> ('a1, 'a2) vect_cons_t eqDec

val eqDec_vect : int -> 'a1 eqDec -> 'a1 vect eqDec

val pow2 : int -> int

module Bits :
 sig
  val rmul : int -> int -> int

  val of_positive : int -> int -> bool vect

  val of_N : int -> int -> bool vect

  val zero : int -> bool vect

  val one : int -> bool vect
 end

type 't finiteType = { finite_index : ('t -> int); finite_elements : 't list }

type 'a show = { show0 : ('a -> char list) }

val show_string : char list show

val list_sum' : int -> int list -> int

val list_sum : int list -> int

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

val assoc :
  'a1 eqDec -> 'a1 -> ('a1 * 'a2) list -> ('a2, ('a1 * 'a2) member) sigT
  option

val list_assoc : 'a1 eqDec -> 'a1 -> ('a1 * 'a2) list -> index option

val list_nth : 'a1 list -> index -> 'a1

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

type 'argKind _Sig = { argSigs : 'argKind vect; retSig : 'argKind }

val cSig_of_Sig : int -> type0 _Sig -> int _Sig

val sig_of_CSig : int -> int _Sig -> type0 _Sig

type externalSignature = type0 _Sig

type 'var_t tsig = ('var_t * type0) list

type ('var_t, 'fn_name_t, 'action) internalFunction = { int_name : 'fn_name_t;
                                                        int_argspec : 
                                                        'var_t tsig;
                                                        int_retSig : 
                                                        type0;
                                                        int_body : 'action }

val map_intf_body :
  ('a3 -> 'a4) -> ('a1, 'a2, 'a3) internalFunction -> ('a1, 'a2, 'a4)
  internalFunction

val eqDec_type : type0 eqDec

type ('k, 'v) context =
| CtxEmpty
| CtxCons of 'k list * 'k * 'v * ('k, 'v) context

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
| UCallModule of (__ -> 'reg_t) * (__, 'ext_fn_t) lift
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

type ext_fn_rtl_spec = { efr_name : char list; efr_internal : bool }

type ext_fn_sim_spec = { efs_name : char list; efs_method : bool }

val empty_Sigma : __ -> externalSignature

val empty_ext_fn_props : __ -> 'a1

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

module ProducerConsumer :
 sig
  val r_sz : int

  type reg_t =
  | Coq_producer_counter
  | Coq_queue_empty
  | Coq_queue_data
  | Coq_output

  val coq_R : reg_t -> type0

  val r : reg_t -> type_denote

  type rule_name_t =
  | Coq_produce
  | Coq_consume

  val rules : rule_name_t -> (pos_t, var_t, fn_name_t, reg_t, __) action

  val pc_scheduler : (pos_t, rule_name_t) scheduler

  val coq_external : rule_name_t -> bool

  val package : interop_package_t
 end

val prog : unit
