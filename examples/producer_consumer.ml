
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Pervasives.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h



(** val pred : int -> int **)

let pred = fun n -> Pervasives.max 0 (n-1)

(** val add : int -> int -> int **)

let rec add = (+)

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Pervasives.max 0 (n-m)

module Nat =
 struct
  (** val pred : int -> int **)

  let pred n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n)
      (fun u -> u)
      n

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

  (** val compare : int -> int -> comparison **)

  let rec compare = fun n m -> if n=m then Eq else if n<m then Lt else Gt

  (** val max : int -> int -> int **)

  let rec max n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n)
        (fun m' -> Pervasives.succ (max n' m'))
        m)
      n

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Pervasives.succ 0)
      (fun m0 -> mul n (pow n m0))
      m

  (** val log2_iter : int -> int -> int -> int -> int **)

  let rec log2_iter k p q r0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> p)
      (fun k' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        log2_iter k' (Pervasives.succ p) (Pervasives.succ q) q)
        (fun r' -> log2_iter k' p (Pervasives.succ q) r')
        r0)
      k

  (** val log2 : int -> int **)

  let log2 n =
    log2_iter (pred n) 0 (Pervasives.succ 0) 0

  (** val log2_up : int -> int **)

  let log2_up a =
    match compare (Pervasives.succ 0) a with
    | Lt -> Pervasives.succ (log2 (pred a))
    | _ -> 0
 end

module N =
 struct
  (** val zero : int **)

  let zero =
    0

  (** val one : int **)

  let one =
    1
 end

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t -> fold_left f t (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t -> f b (fold_right f a0 t)

(** val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let rec combine l l' =
  match l with
  | [] -> []
  | x :: tl ->
    (match l' with
     | [] -> []
     | y :: tl' -> (x, y) :: (combine tl tl'))

(** val skipn : int -> 'a1 list -> 'a1 list **)

let rec skipn n l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n0 -> match l with
               | [] -> []
               | _ :: l0 -> skipn n0 l0)
    n

(** val length0 : char list -> int **)

let rec length0 = function
| [] -> 0
| _::s' -> Pervasives.succ (length0 s')

type 't eqDec = { eq_dec : ('t -> 't -> bool) }

(** val beq_dec : 'a1 eqDec -> 'a1 -> 'a1 -> bool **)

let beq_dec eQ a1 a2 =
  if eQ.eq_dec a1 a2 then true else false

(** val eqDec_bool : bool eqDec **)

let eqDec_bool =
  { eq_dec = (fun t1 t2 ->
    if t1 then if t2 then true else false else if t2 then false else true) }

(** val eqDec_ascii : char eqDec **)

let eqDec_ascii =
  { eq_dec = (fun t1 t2 ->
    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
      (fun x x0 x1 x2 x3 x4 x5 x6 ->
      (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
        (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
        if eqDec_bool.eq_dec x b7
        then if eqDec_bool.eq_dec x0 b8
             then if eqDec_bool.eq_dec x1 b9
                  then if eqDec_bool.eq_dec x2 b10
                       then if eqDec_bool.eq_dec x3 b11
                            then if eqDec_bool.eq_dec x4 b12
                                 then if eqDec_bool.eq_dec x5 b13
                                      then eqDec_bool.eq_dec x6 b14
                                      else false
                                 else false
                            else false
                       else false
                  else false
             else false
        else false)
        t2)
      t1) }

(** val eqDec_string : char list eqDec **)

let eqDec_string =
  { eq_dec = (fun t1 t2 ->
    let rec f s x =
      match s with
      | [] -> (match x with
               | [] -> true
               | _::_ -> false)
      | a::s0 ->
        (match x with
         | [] -> false
         | a0::s1 -> if eqDec_ascii.eq_dec a a0 then f s0 s1 else false)
    in f t1 t2) }

(** val eqDec_nat : int eqDec **)

let eqDec_nat =
  { eq_dec = (=) }

type index = int

(** val index_of_nat : int -> int -> index option **)

let rec index_of_nat = fun sz x -> if x < sz then Some x else None

(** val index_to_nat : int -> index -> int **)

let rec index_to_nat = fun _ x -> x

type ('a, 'b) vect_cons_t = { vhd : 'a; vtl : 'b }

type 't vect = __

(** val vect_hd : int -> ('a1, __) vect_cons_t -> 'a1 **)

let vect_hd _ v =
  v.vhd

(** val vect_tl : int -> ('a1, __) vect_cons_t -> 'a1 vect **)

let vect_tl _ v =
  v.vtl

(** val vect_cons : int -> 'a1 -> 'a1 vect -> ('a1, __) vect_cons_t **)

let vect_cons _ t v =
  { vhd = t; vtl = v }

(** val vect_const : int -> 'a1 -> 'a1 vect **)

let rec vect_const sz t =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic __)
    (fun sz0 -> Obj.magic vect_cons sz0 t (vect_const sz0 t))
    sz

(** val vect_nth : int -> 'a1 vect -> index -> 'a1 **)

let rec vect_nth n v idx =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> assert false (* absurd case *))
    (fun n0 ->
    (fun fthisone fanotherone n -> if n = 0 then fthisone () else fanotherone (n - 1))
      (fun _ -> vect_hd n0 (Obj.magic v))
      (fun idx0 -> vect_nth n0 (vect_tl n0 (Obj.magic v)) idx0)
      (Obj.magic idx))
    n

(** val vect_map : int -> ('a1 -> 'a2) -> 'a1 vect -> 'a2 vect **)

let rec vect_map n f v =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic __ v)
    (fun n0 ->
    Obj.magic vect_cons n0 (f (vect_hd n0 (Obj.magic v)))
      (vect_map n0 f (vect_tl n0 (Obj.magic v))))
    n

(** val vect_find_index : int -> ('a1 -> bool) -> 'a1 vect -> index option **)

let rec vect_find_index sz f v =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic None)
    (fun n ->
    if f (vect_hd n (Obj.magic v))
    then Some (Obj.magic 0)
    else (match vect_find_index n f (vect_tl n (Obj.magic v)) with
          | Some idx -> Some (Obj.magic (Pervasives.succ idx))
          | None -> None))
    sz

(** val vect_index : int -> 'a1 eqDec -> 'a1 -> 'a1 vect -> index option **)

let vect_index sz eQ k v =
  vect_find_index sz (fun t -> beq_dec eQ t k) v

(** val eqDec_vect_nil : 'a1 eqDec -> __ eqDec **)

let eqDec_vect_nil _ =
  { eq_dec = (fun _ _ -> true) }

(** val eqDec_vect_cons :
    'a1 eqDec -> 'a2 eqDec -> ('a1, 'a2) vect_cons_t eqDec **)

let eqDec_vect_cons h h0 =
  { eq_dec = (fun t1 t2 ->
    let vhd0 = t1.vhd in
    let vtl0 = t1.vtl in
    let vhd1 = t2.vhd in
    let vtl1 = t2.vtl in
    if h.eq_dec vhd0 vhd1 then h0.eq_dec vtl0 vtl1 else false) }

(** val eqDec_vect : int -> 'a1 eqDec -> 'a1 vect eqDec **)

let rec eqDec_vect n h =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic eqDec_vect_nil h)
    (fun n0 -> Obj.magic eqDec_vect_cons h (eqDec_vect n0 h))
    n

(** val pow2 : int -> int **)

let pow2 n =
  Pervasives.succ (pred (Nat.pow (Pervasives.succ (Pervasives.succ 0)) n))

module Bits =
 struct
  (** val rmul : int -> int -> int **)

  let rec rmul n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add (rmul p m) m)
      n

  (** val of_positive : int -> int -> bool vect **)

  let rec of_positive sz p =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Obj.magic __)
      (fun sz0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 ->
        Obj.magic vect_cons sz0 true (of_positive sz0 p0))
        (fun p0 ->
        Obj.magic vect_cons sz0 false (of_positive sz0 p0))
        (fun _ -> Obj.magic vect_cons sz0 true (vect_const sz0 false))
        p)
      sz

  (** val of_N : int -> int -> bool vect **)

  let of_N sz n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> vect_const sz false)
      (fun p -> of_positive sz p)
      n

  (** val zero : int -> bool vect **)

  let zero sz =
    of_N sz N.zero

  (** val one : int -> bool vect **)

  let one sz =
    of_N sz N.one
 end

type 't finiteType = { finite_index : ('t -> int); finite_elements : 't list }

type 'a show = { show0 : ('a -> char list) }

(** val show_string : char list show **)

let show_string =
  { show0 = (fun x -> x) }

(** val list_sum' : int -> int list -> int **)

let list_sum' n l =
  fold_right (fun x acc -> add acc x) n l

(** val list_sum : int list -> int **)

let list_sum l =
  list_sum' 0 l

type ('s, 'f) result =
| Success of 's
| Failure of 'f

(** val result_map_failure :
    ('a2 -> 'a3) -> ('a1, 'a2) result -> ('a1, 'a3) result **)

let result_map_failure fn = function
| Success s -> Success s
| Failure f -> Failure (fn f)

(** val opt_result : 'a1 option -> 'a2 -> ('a1, 'a2) result **)

let opt_result o f =
  match o with
  | Some x -> Success x
  | None -> Failure f

(** val result_list_map :
    ('a1 -> ('a2, 'a3) result) -> 'a1 list -> ('a2 list, 'a3) result **)

let rec result_list_map f = function
| [] -> Success []
| a :: la0 ->
  (match f a with
   | Success b ->
     (match result_list_map f la0 with
      | Success la1 -> Success (b :: la1)
      | Failure f0 -> Failure f0)
   | Failure f0 -> Failure f0)

(** val extract_success : ('a1, 'a2) result -> 'a1 **)

let extract_success = function
| Success s -> s
| Failure _ -> assert false (* absurd case *)

type 'k member =
| MemberHd of 'k * 'k list
| MemberTl of 'k * 'k * 'k list * 'k member

(** val assoc :
    'a1 eqDec -> 'a1 -> ('a1 * 'a2) list -> ('a2, ('a1 * 'a2) member) sigT
    option **)

let rec assoc h k1 = function
| [] -> None
| p :: x ->
  let (k1', k2) = p in
  let s = h.eq_dec k1 k1' in
  if s
  then Some (ExistT (k2, (MemberHd ((k1', k2), x))))
  else let o = assoc h k1 x in
       (match o with
        | Some s0 ->
          let ExistT (k2', m) = s0 in
          Some (ExistT (k2', (MemberTl ((k1, k2'), (k1', k2), x, m))))
        | None -> None)

(** val list_assoc : 'a1 eqDec -> 'a1 -> ('a1 * 'a2) list -> index option **)

let rec list_assoc eQ k = function
| [] -> None
| h :: l0 ->
  let s = eQ.eq_dec k (fst h) in
  if s
  then Some (Obj.magic 0)
  else let o = list_assoc eQ k l0 in
       (match o with
        | Some i -> Some (Obj.magic (Pervasives.succ i))
        | None -> None)

(** val list_nth : 'a1 list -> index -> 'a1 **)

let rec list_nth l idx =
  match l with
  | [] -> assert false (* absurd case *)
  | h :: l0 ->
    ((fun fthisone fanotherone n -> if n = 0 then fthisone () else fanotherone (n - 1))
       (fun _ -> h)
       (fun a -> list_nth l0 a)
       (Obj.magic idx))

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

(** val kind_of_type : type0 -> type_kind **)

let kind_of_type = function
| Bits_t _ -> Kind_bits
| Enum_t sig0 -> Kind_enum (Some sig0)
| Struct_t sig0 -> Kind_struct (Some sig0)
| Array_t sig0 -> Kind_array (Some sig0)

(** val struct_fields_sz' :
    (type0 -> int) -> (char list * type0) list -> int **)

let struct_fields_sz' type_sz0 fields =
  list_sum (map (fun nm_tau -> type_sz0 (snd nm_tau)) fields)

(** val type_sz : type0 -> int **)

let rec type_sz = function
| Bits_t sz -> sz
| Enum_t sig0 -> sig0.enum_bitsize
| Struct_t sig0 -> struct_fields_sz' type_sz sig0.struct_fields
| Array_t sig0 -> Bits.rmul sig0.array_len (type_sz sig0.array_type)

type struct_index = index

(** val struct_sz : type0 struct_sig' -> int **)

let struct_sz sig0 =
  type_sz (Struct_t sig0)

(** val field_type : type0 struct_sig' -> index -> type0 **)

let field_type sig0 idx =
  snd (list_nth sig0.struct_fields idx)

(** val field_sz : type0 struct_sig' -> index -> int **)

let field_sz sig0 idx =
  type_sz (field_type sig0 idx)

(** val field_offset_right : type0 struct_sig' -> struct_index -> int **)

let field_offset_right sig0 idx =
  let next_fields =
    skipn (Pervasives.succ (index_to_nat (length sig0.struct_fields) idx))
      sig0.struct_fields
  in
  struct_fields_sz' type_sz next_fields

type array_index = index

(** val array_sz : type0 array_sig' -> int **)

let array_sz sig0 =
  type_sz (Array_t sig0)

(** val element_sz : type0 array_sig' -> int **)

let element_sz sig0 =
  type_sz sig0.array_type

(** val element_offset_right : type0 array_sig' -> array_index -> int **)

let element_offset_right sig0 idx =
  Bits.rmul
    (sub sig0.array_len (Pervasives.succ (index_to_nat sig0.array_len idx)))
    (element_sz sig0)

type port =
| P0
| P1

type type_denote = __

type 'argKind _Sig = { argSigs : 'argKind vect; retSig : 'argKind }

(** val cSig_of_Sig : int -> type0 _Sig -> int _Sig **)

let cSig_of_Sig n sig0 =
  { argSigs = (vect_map n type_sz sig0.argSigs); retSig =
    (type_sz sig0.retSig) }

(** val sig_of_CSig : int -> int _Sig -> type0 _Sig **)

let sig_of_CSig n sig0 =
  { argSigs = (vect_map n (fun x -> Bits_t x) sig0.argSigs); retSig = (Bits_t
    sig0.retSig) }

type externalSignature = type0 _Sig

type 'var_t tsig = ('var_t * type0) list

type ('var_t, 'fn_name_t, 'action) internalFunction = { int_name : 'fn_name_t;
                                                        int_argspec : 
                                                        'var_t tsig;
                                                        int_retSig : 
                                                        type0;
                                                        int_body : 'action }

(** val map_intf_body :
    ('a3 -> 'a4) -> ('a1, 'a2, 'a3) internalFunction -> ('a1, 'a2, 'a4)
    internalFunction **)

let map_intf_body f fn =
  { int_name = fn.int_name; int_argspec = fn.int_argspec; int_retSig =
    fn.int_retSig; int_body = (f fn.int_body) }

(** val eqDec_type : type0 eqDec **)

let eqDec_type =
  { eq_dec =
    (let rec iHtau t1 t2 =
       match t1 with
       | Bits_t sz1 ->
         (match t2 with
          | Bits_t sz2 -> eqDec_nat.eq_dec sz1 sz2
          | _ -> false)
       | Enum_t en1 ->
         (match t2 with
          | Enum_t en2 ->
            let { enum_name = en3; enum_size = es1; enum_bitsize = ebsz1;
              enum_members = em1; enum_bitpatterns = ebp1 } = en1
            in
            let { enum_name = en4; enum_size = es2; enum_bitsize = ebsz2;
              enum_members = em2; enum_bitpatterns = ebp2 } = en2
            in
            let s = eqDec_string.eq_dec en3 en4 in
            if s
            then let s0 = eqDec_nat.eq_dec es1 es2 in
                 if s0
                 then let s1 = eqDec_nat.eq_dec ebsz1 ebsz2 in
                      if s1
                      then let s2 =
                             (eqDec_vect es2 eqDec_string).eq_dec em1 em2
                           in
                           if s2
                           then (eqDec_vect es2 (eqDec_vect ebsz2 eqDec_bool)).eq_dec
                                  ebp1 ebp2
                           else false
                      else false
                 else false
            else false
          | _ -> false)
       | Struct_t fs1 ->
         (match t2 with
          | Struct_t fs2 ->
            let { struct_name = nm1; struct_fields = f1 } = fs1 in
            let { struct_name = nm2; struct_fields = f2 } = fs2 in
            let s = eqDec_string.eq_dec nm1 nm2 in
            if s
            then let rec f l x =
                   match l with
                   | [] -> (match x with
                            | [] -> true
                            | _ :: _ -> false)
                   | y :: l0 ->
                     (match x with
                      | [] -> false
                      | p :: l1 ->
                        if let (x0, x1) = y in
                           let (s0, t) = p in
                           if eqDec_string.eq_dec x0 s0
                           then iHtau x1 t
                           else false
                        then f l0 l1
                        else false)
                 in f f1 f2
            else false
          | _ -> false)
       | Array_t as1 ->
         (match t2 with
          | Array_t as2 ->
            let { array_type = tau1; array_len = len1 } = as1 in
            let { array_type = tau2; array_len = len2 } = as2 in
            let s = iHtau tau1 tau2 in
            if s then eqDec_nat.eq_dec len1 len2 else false
          | _ -> false)
     in iHtau) }

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

(** val assert_kind :
    type_kind -> fn_tc_error_loc -> type0 -> (__, fn_tc_error) result **)

let assert_kind kind arg tau =
  match kind with
  | Kind_bits ->
    (match tau with
     | Bits_t sz -> Success (Obj.magic sz)
     | _ -> Failure (arg, (KindMismatch ((kind_of_type tau), kind))))
  | Kind_enum _ ->
    (match tau with
     | Enum_t sg -> Success (Obj.magic sg)
     | _ -> Failure (arg, (KindMismatch ((kind_of_type tau), kind))))
  | Kind_struct _ ->
    (match tau with
     | Struct_t sg -> Success (Obj.magic sg)
     | _ -> Failure (arg, (KindMismatch ((kind_of_type tau), kind))))
  | Kind_array _ ->
    (match tau with
     | Array_t sg -> Success (Obj.magic sg)
     | _ -> Failure (arg, (KindMismatch ((kind_of_type tau), kind))))

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

module PrimUntyped =
 struct
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

  (** val coq_GetElementBits : type0 array_sig' -> array_index -> fbits1 **)

  let coq_GetElementBits sig0 idx =
    Slice ((array_sz sig0), (element_offset_right sig0 idx),
      (element_sz sig0))

  (** val coq_SubstElementBits : type0 array_sig' -> array_index -> fbits2 **)

  let coq_SubstElementBits sig0 idx =
    SliceSubst ((array_sz sig0), (element_offset_right sig0 idx),
      (element_sz sig0))

  (** val coq_GetFieldBits : type0 struct_sig' -> struct_index -> fbits1 **)

  let coq_GetFieldBits sig0 idx =
    Slice ((struct_sz sig0), (field_offset_right sig0 idx),
      (field_sz sig0 idx))

  (** val coq_SubstFieldBits : type0 struct_sig' -> struct_index -> fbits2 **)

  let coq_SubstFieldBits sig0 idx =
    SliceSubst ((struct_sz sig0), (field_offset_right sig0 idx),
      (field_sz sig0 idx))
 end

module PrimTypeInference =
 struct
  (** val find_field :
      type0 struct_sig' -> char list -> (index, fn_tc_error) result **)

  let find_field sig0 f =
    opt_result (list_assoc eqDec_string f sig0.struct_fields) (Arg1,
      (UnboundField (f, sig0)))

  (** val check_index :
      type0 array_sig' -> int -> (array_index, fn_tc_error) result **)

  let check_index sig0 pos =
    opt_result (index_of_nat sig0.array_len pos) (Arg1, (OutOfBounds (pos,
      sig0)))

  (** val tc1 :
      PrimUntyped.ufn1 -> type0 -> (PrimTyped.fn1, fn_tc_error) result **)

  let tc1 fn tau1 =
    match fn with
    | PrimUntyped.UDisplay fn0 ->
      (match fn0 with
       | PrimUntyped.UDisplayUtf8 ->
         (match assert_kind (Kind_array None) Arg1 tau1 with
          | Success sig0 ->
            Success (PrimTyped.Display (PrimTyped.DisplayUtf8
              (Obj.magic sig0).array_len))
          | Failure f -> Failure f)
       | PrimUntyped.UDisplayValue opts ->
         Success (PrimTyped.Display (PrimTyped.DisplayValue (tau1, opts))))
    | PrimUntyped.UConv fn0 ->
      Success
        (match fn0 with
         | PrimUntyped.UPack -> PrimTyped.Conv (tau1, PrimTyped.Pack)
         | PrimUntyped.UUnpack tau -> PrimTyped.Conv (tau, PrimTyped.Unpack)
         | PrimUntyped.UIgnore -> PrimTyped.Conv (tau1, PrimTyped.Ignore))
    | PrimUntyped.UBits1 fn0 ->
      (match assert_kind Kind_bits Arg1 tau1 with
       | Success sz1 ->
         Success (PrimTyped.Bits1
           (match fn0 with
            | PrimUntyped.UNot -> PrimTyped.Not (Obj.magic sz1)
            | PrimUntyped.USExt width ->
              PrimTyped.SExt ((Obj.magic sz1), width)
            | PrimUntyped.UZExtL width ->
              PrimTyped.ZExtL ((Obj.magic sz1), width)
            | PrimUntyped.UZExtR width ->
              PrimTyped.ZExtR ((Obj.magic sz1), width)
            | PrimUntyped.URepeat times ->
              PrimTyped.Repeat ((Obj.magic sz1), times)
            | PrimUntyped.USlice (offset, width) ->
              PrimTyped.Slice ((Obj.magic sz1), offset, width)))
       | Failure f -> Failure f)
    | PrimUntyped.UStruct1 fn0 ->
      (match fn0 with
       | PrimUntyped.UGetField f ->
         (match assert_kind (Kind_struct None) Arg1 tau1 with
          | Success sig0 ->
            (match find_field (Obj.magic sig0) f with
             | Success idx ->
               Success (PrimTyped.Struct1 ((Obj.magic sig0), idx))
             | Failure f0 -> Failure f0)
          | Failure f0 -> Failure f0)
       | PrimUntyped.UGetFieldBits (sig0, f) ->
         (match find_field sig0 f with
          | Success idx ->
            Success (PrimTyped.Bits1 (PrimTyped.coq_GetFieldBits sig0 idx))
          | Failure f0 -> Failure f0))
    | PrimUntyped.UArray1 fn0 ->
      (match fn0 with
       | PrimUntyped.UGetElement pos ->
         (match assert_kind (Kind_array None) Arg1 tau1 with
          | Success sig0 ->
            (match check_index (Obj.magic sig0) pos with
             | Success idx ->
               Success (PrimTyped.Array1 ((Obj.magic sig0), idx))
             | Failure f -> Failure f)
          | Failure f -> Failure f)
       | PrimUntyped.UGetElementBits (sig0, pos) ->
         (match check_index sig0 pos with
          | Success idx ->
            Success (PrimTyped.Bits1 (PrimTyped.coq_GetElementBits sig0 idx))
          | Failure f -> Failure f))

  (** val tc2 :
      PrimUntyped.ufn2 -> type0 -> type0 -> (PrimTyped.fn2, fn_tc_error)
      result **)

  let tc2 fn tau1 tau2 =
    match fn with
    | PrimUntyped.UEq negate -> Success (PrimTyped.Eq (tau1, negate))
    | PrimUntyped.UBits2 fn0 ->
      (match assert_kind Kind_bits Arg1 tau1 with
       | Success sz1 ->
         (match assert_kind Kind_bits Arg2 tau2 with
          | Success sz2 ->
            Success (PrimTyped.Bits2
              (match fn0 with
               | PrimUntyped.UAnd -> PrimTyped.And (Obj.magic sz1)
               | PrimUntyped.UOr -> PrimTyped.Or (Obj.magic sz1)
               | PrimUntyped.UXor -> PrimTyped.Xor (Obj.magic sz1)
               | PrimUntyped.ULsl ->
                 PrimTyped.Lsl ((Obj.magic sz1), (Obj.magic sz2))
               | PrimUntyped.ULsr ->
                 PrimTyped.Lsr ((Obj.magic sz1), (Obj.magic sz2))
               | PrimUntyped.UAsr ->
                 PrimTyped.Asr ((Obj.magic sz1), (Obj.magic sz2))
               | PrimUntyped.UConcat ->
                 PrimTyped.Concat ((Obj.magic sz1), (Obj.magic sz2))
               | PrimUntyped.USel -> PrimTyped.Sel (Obj.magic sz1)
               | PrimUntyped.USliceSubst (offset, width) ->
                 PrimTyped.SliceSubst ((Obj.magic sz1), offset, width)
               | PrimUntyped.UIndexedSlice width ->
                 PrimTyped.IndexedSlice ((Obj.magic sz1), width)
               | PrimUntyped.UPlus -> PrimTyped.Plus (Obj.magic sz1)
               | PrimUntyped.UMinus -> PrimTyped.Minus (Obj.magic sz1)
               | PrimUntyped.UMul ->
                 PrimTyped.Mul ((Obj.magic sz1), (Obj.magic sz2))
               | PrimUntyped.UCompare (signed, c) ->
                 PrimTyped.Compare (signed, c, (Obj.magic sz1))))
          | Failure f -> Failure f)
       | Failure f -> Failure f)
    | PrimUntyped.UStruct2 fn0 ->
      (match fn0 with
       | PrimUntyped.USubstField f ->
         (match assert_kind (Kind_struct None) Arg1 tau1 with
          | Success sig0 ->
            (match find_field (Obj.magic sig0) f with
             | Success idx ->
               Success (PrimTyped.Struct2 ((Obj.magic sig0), idx))
             | Failure f0 -> Failure f0)
          | Failure f0 -> Failure f0)
       | PrimUntyped.USubstFieldBits (sig0, f) ->
         (match find_field sig0 f with
          | Success idx ->
            Success (PrimTyped.Bits2 (PrimTyped.coq_SubstFieldBits sig0 idx))
          | Failure f0 -> Failure f0))
    | PrimUntyped.UArray2 fn0 ->
      (match fn0 with
       | PrimUntyped.USubstElement pos ->
         (match assert_kind (Kind_array None) Arg1 tau1 with
          | Success sig0 ->
            (match check_index (Obj.magic sig0) pos with
             | Success idx ->
               Success (PrimTyped.Array2 ((Obj.magic sig0), idx))
             | Failure f -> Failure f)
          | Failure f -> Failure f)
       | PrimUntyped.USubstElementBits (sig0, pos) ->
         (match check_index sig0 pos with
          | Success idx ->
            Success (PrimTyped.Bits2
              (PrimTyped.coq_SubstElementBits sig0 idx))
          | Failure f -> Failure f))
 end

module CircuitSignatures =
 struct
  (** val coq_DisplaySigma : PrimTyped.fdisplay -> type0 _Sig **)

  let coq_DisplaySigma fn =
    { argSigs =
      (Obj.magic vect_cons 0
        (match fn with
         | PrimTyped.DisplayUtf8 len ->
           Array_t { array_type = (Bits_t (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))));
             array_len = len }
         | PrimTyped.DisplayValue (tau, _) -> tau) __); retSig = (Bits_t 0) }

  (** val coq_CSigma1 : PrimTyped.fbits1 -> int _Sig **)

  let coq_CSigma1 = function
  | PrimTyped.Not sz ->
    { argSigs = (Obj.magic vect_cons 0 sz __); retSig = sz }
  | PrimTyped.SExt (sz, width) ->
    { argSigs = (Obj.magic vect_cons 0 sz __); retSig = (Nat.max sz width) }
  | PrimTyped.ZExtL (sz, width) ->
    { argSigs = (Obj.magic vect_cons 0 sz __); retSig = (Nat.max sz width) }
  | PrimTyped.ZExtR (sz, width) ->
    { argSigs = (Obj.magic vect_cons 0 sz __); retSig = (Nat.max sz width) }
  | PrimTyped.Repeat (sz, times) ->
    { argSigs = (Obj.magic vect_cons 0 sz __); retSig = (mul times sz) }
  | PrimTyped.Slice (sz, _, width) ->
    { argSigs = (Obj.magic vect_cons 0 sz __); retSig = width }
  | PrimTyped.Lowered fn0 ->
    (match fn0 with
     | PrimTyped.IgnoreBits sz ->
       { argSigs = (Obj.magic vect_cons 0 sz __); retSig = 0 }
     | PrimTyped.DisplayBits fn3 ->
       cSig_of_Sig (Pervasives.succ 0) (coq_DisplaySigma fn3))

  (** val coq_CSigma2 : PrimTyped.fbits2 -> int _Sig **)

  let coq_CSigma2 = function
  | PrimTyped.And sz ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz
        (vect_cons 0 sz (Obj.magic __))); retSig = sz }
  | PrimTyped.Or sz ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz
        (vect_cons 0 sz (Obj.magic __))); retSig = sz }
  | PrimTyped.Xor sz ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz
        (vect_cons 0 sz (Obj.magic __))); retSig = sz }
  | PrimTyped.Lsl (bits_sz, shift_sz) ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) bits_sz
        (vect_cons 0 shift_sz (Obj.magic __))); retSig = bits_sz }
  | PrimTyped.Lsr (bits_sz, shift_sz) ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) bits_sz
        (vect_cons 0 shift_sz (Obj.magic __))); retSig = bits_sz }
  | PrimTyped.Asr (bits_sz, shift_sz) ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) bits_sz
        (vect_cons 0 shift_sz (Obj.magic __))); retSig = bits_sz }
  | PrimTyped.Concat (sz1, sz2) ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz1
        (vect_cons 0 sz2 (Obj.magic __))); retSig = (add sz2 sz1) }
  | PrimTyped.Sel sz ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz
        (vect_cons 0 (Nat.log2_up sz) (Obj.magic __))); retSig =
      (Pervasives.succ 0) }
  | PrimTyped.SliceSubst (sz, _, width) ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz
        (vect_cons 0 width (Obj.magic __))); retSig = sz }
  | PrimTyped.IndexedSlice (sz, width) ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz
        (vect_cons 0 (Nat.log2_up sz) (Obj.magic __))); retSig = width }
  | PrimTyped.Plus sz ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz
        (vect_cons 0 sz (Obj.magic __))); retSig = sz }
  | PrimTyped.Minus sz ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz
        (vect_cons 0 sz (Obj.magic __))); retSig = sz }
  | PrimTyped.Mul (sz1, sz2) ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz1
        (vect_cons 0 sz2 (Obj.magic __))); retSig = (add sz1 sz2) }
  | PrimTyped.EqBits (sz, _) ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz
        (vect_cons 0 sz (Obj.magic __))); retSig = (Pervasives.succ 0) }
  | PrimTyped.Compare (_, _, sz) ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz
        (vect_cons 0 sz (Obj.magic __))); retSig = (Pervasives.succ 0) }
 end

module PrimSignatures =
 struct
  (** val coq_Sigma1 : PrimTyped.fn1 -> type0 _Sig **)

  let coq_Sigma1 = function
  | PrimTyped.Display fn0 -> CircuitSignatures.coq_DisplaySigma fn0
  | PrimTyped.Conv (tau, fn0) ->
    (match fn0 with
     | PrimTyped.Pack ->
       { argSigs = (Obj.magic vect_cons 0 tau __); retSig = (Bits_t
         (type_sz tau)) }
     | PrimTyped.Unpack ->
       { argSigs = (Obj.magic vect_cons 0 (Bits_t (type_sz tau)) __);
         retSig = tau }
     | PrimTyped.Ignore ->
       { argSigs = (Obj.magic vect_cons 0 tau __); retSig = (Bits_t 0) })
  | PrimTyped.Bits1 fn0 ->
    sig_of_CSig (Pervasives.succ 0) (CircuitSignatures.coq_CSigma1 fn0)
  | PrimTyped.Struct1 (sig0, idx) ->
    { argSigs = (Obj.magic vect_cons 0 (Struct_t sig0) __); retSig =
      (field_type sig0 idx) }
  | PrimTyped.Array1 (sig0, _) ->
    { argSigs = (Obj.magic vect_cons 0 (Array_t sig0) __); retSig =
      sig0.array_type }

  (** val coq_Sigma2 : PrimTyped.fn2 -> type0 _Sig **)

  let coq_Sigma2 = function
  | PrimTyped.Eq (tau, _) ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) tau
        (vect_cons 0 tau (Obj.magic __))); retSig = (Bits_t (Pervasives.succ
      0)) }
  | PrimTyped.Bits2 fn0 ->
    sig_of_CSig (Pervasives.succ (Pervasives.succ 0))
      (CircuitSignatures.coq_CSigma2 fn0)
  | PrimTyped.Struct2 (sig0, idx) ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) (Struct_t sig0)
        (vect_cons 0 (field_type sig0 idx) (Obj.magic __))); retSig =
      (Struct_t sig0) }
  | PrimTyped.Array2 (sig0, _) ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) (Array_t sig0)
        (vect_cons 0 sig0.array_type (Obj.magic __))); retSig = (Array_t
      sig0) }
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

(** val bits_of_ascii :
    char -> (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, __)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t **)

let bits_of_ascii c =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b0 b1 b2 b3 b4 b5 b6 b7 ->
    Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0))))))) b0
      (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) b1
        (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))) b2
          (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ 0)))) b3
            (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
              (Pervasives.succ 0))) b4
              (vect_cons (Pervasives.succ (Pervasives.succ 0)) b5
                (Obj.magic vect_cons (Pervasives.succ 0) b6
                  (vect_cons 0 b7 (Obj.magic __)))))))))
    c

(** val array_of_bytes :
    char list -> (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, __)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t vect **)

let rec array_of_bytes = function
| [] -> Obj.magic __
| c::s0 ->
  Obj.magic vect_cons (length0 s0) (bits_of_ascii c) (array_of_bytes s0)

(** val uprogn :
    ('a1, 'a2, 'a3, 'a4, 'a5) uaction list -> ('a1, 'a2, 'a3, 'a4, 'a5)
    uaction **)

let rec uprogn = function
| [] -> UConst ((Bits_t 0), (Obj.magic __))
| a :: aa0 -> (match aa0 with
               | [] -> a
               | _ :: _ -> USeq (a, (uprogn aa0)))

(** val uskip : ('a1, 'a2, 'a3, 'a4, 'a5) uaction **)

let uskip =
  UConst ((Bits_t 0), (Obj.magic __))

(** val uinit : type0 -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction **)

let uinit tau =
  let zeroes = UConst ((Bits_t (type_sz tau)),
    (vect_const (type_sz tau) false))
  in
  UUnop ((PrimUntyped.UConv (PrimUntyped.UUnpack tau)), zeroes)

(** val ustruct_init :
    type0 struct_sig' -> (char list * ('a1, 'a2, 'a3, 'a4, 'a5) uaction) list
    -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction **)

let ustruct_init sig0 fields =
  let empty = uinit (Struct_t sig0) in
  let usubst = fun f x x0 -> UBinop ((PrimUntyped.UStruct2
    (PrimUntyped.USubstField f)), x, x0)
  in
  fold_left (fun acc pat -> let (f, a) = pat in usubst f acc a) fields empty

(** val uswitch :
    ('a1, 'a2, 'a3, 'a4, 'a5) uaction -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction ->
    (('a1, 'a2, 'a3, 'a4, 'a5) uaction * ('a1, 'a2, 'a3, 'a4, 'a5) uaction)
    list -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction **)

let rec uswitch var default = function
| [] -> default
| p :: branches0 ->
  let (label, action0) = p in
  UIf ((UBinop ((PrimUntyped.UEq false), var, label)), action0,
  (uswitch var default branches0))

(** val desugar_action' :
    'a1 -> ('a6 -> 'a4) -> ('a7 -> 'a5) -> ('a1, 'a2, 'a3, 'a6, 'a7) uaction
    -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction **)

let desugar_action' =
  let rec desugar_action'0 pos fR fSigma a =
    let d = fun a0 -> desugar_action'0 pos fR fSigma a0 in
    (match a with
     | UError err -> UError err
     | UFail tau -> UFail tau
     | UVar var -> UVar var
     | UConst (tau, cst) -> UConst (tau, cst)
     | UAssign (v, ex) -> UAssign (v, (d ex))
     | USeq (a1, a2) -> USeq ((d a1), (d a2))
     | UBind (v, ex, body) -> UBind (v, (d ex), (d body))
     | UIf (cond, tbranch, fbranch) ->
       UIf ((d cond), (d tbranch), (d fbranch))
     | URead (port0, idx) -> URead (port0, (fR idx))
     | UWrite (port0, idx, value) -> UWrite (port0, (fR idx), (d value))
     | UUnop (fn, arg) -> UUnop (fn, (d arg))
     | UBinop (fn, arg1, arg2) -> UBinop (fn, (d arg1), (d arg2))
     | UExternalCall (fn, arg) -> UExternalCall ((fSigma fn), (d arg))
     | UInternalCall (fn, args) ->
       UInternalCall ((map_intf_body d fn), (map d args))
     | UAPos (p, e) -> UAPos (p, (d e))
     | USugar s -> desugar __ __ pos fR fSigma s)
  and desugar _ _ pos fR fSigma s =
    let d = fun a -> desugar_action'0 pos fR fSigma a in
    (match s with
     | UErrorInAst -> UError { epos = pos; emsg = ExplicitErrorInAst }
     | USkip -> uskip
     | UConstBits (sz, bs) -> UConst ((Bits_t sz), bs)
     | UConstString s0 ->
       UConst ((Array_t { array_type = (Bits_t (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))));
         array_len = (length0 s0) }), (array_of_bytes s0))
     | UConstEnum (sig0, name) ->
       (match vect_index sig0.enum_size eqDec_string name sig0.enum_members with
        | Some idx ->
          UConst ((Enum_t sig0),
            (vect_nth sig0.enum_size sig0.enum_bitpatterns idx))
        | None ->
          UError { epos = pos; emsg = (UnboundEnumMember (name, sig0)) })
     | UProgn aa -> uprogn (map d aa)
     | ULet (bindings, body) ->
       fold_right (fun pat acc ->
         let (var, a) = pat in UBind (var, (d a), acc)) (d body) bindings
     | UWhen (cond, body) -> UIf ((d cond), (d body), (UFail (Bits_t 0)))
     | USwitch (var, default, branches) ->
       let branches0 =
         map (fun pat -> let (cond, body) = pat in ((d cond), (d body)))
           branches
       in
       uswitch (d var) (d default) branches0
     | UStructInit (sig0, fields) ->
       let fields0 = map (fun pat -> let (f, a) = pat in (f, (d a))) fields in
       ustruct_init sig0 fields0
     | UArrayInit (tau, elements) ->
       let sig0 = { array_type = tau; array_len = (length elements) } in
       let usubst = fun pos0 x x0 -> UBinop ((PrimUntyped.UArray2
         (PrimUntyped.USubstElement pos0)), x, x0)
       in
       let empty = uinit (Array_t sig0) in
       snd
         (fold_left (fun pat a ->
           let (pos0, acc) = pat in
           ((Pervasives.succ pos0), (usubst pos0 acc (d a)))) elements (0,
           empty))
     | UCallModule (fR', fSigma', fn, args) ->
       let df = fun body ->
         Obj.magic desugar_action'0 pos (fun r0 -> fR (fR' r0)) (fun fn0 ->
           fSigma (fSigma' fn0)) body
       in
       UInternalCall ((map_intf_body df fn), (map d args)))
  in desugar_action'0

(** val desugar_action :
    'a1 -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction -> ('a1, 'a2, 'a3, 'a4, 'a5)
    uaction **)

let desugar_action pos a =
  desugar_action' pos (fun r0 -> r0) (fun fn -> fn) a

(** val lift_basic_error_message :
    ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a1 -> 'a2 tsig -> type0
    -> ('a1, 'a2, 'a3, 'a4, 'a5) action -> basic_error_message -> ('a1, 'a2,
    'a3) error **)

let lift_basic_error_message _ _ pos _ _ _ err =
  { epos = pos; emsg = (BasicError err) }

(** val lift_fn1_tc_result :
    ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a2 tsig -> type0 -> 'a1
    -> ('a1, 'a2, 'a3, 'a4, 'a5) action -> ('a6, fn_tc_error) result -> ('a6,
    ('a1, 'a2, 'a3) error) result **)

let lift_fn1_tc_result r0 sigma sig0 tau pos e r1 =
  result_map_failure (fun pat ->
    let (_, err) = pat in lift_basic_error_message r0 sigma pos sig0 tau e err)
    r1

(** val lift_fn2_tc_result :
    ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a2 tsig -> type0 -> 'a2
    tsig -> type0 -> 'a1 -> ('a1, 'a2, 'a3, 'a4, 'a5) action -> 'a1 -> ('a1,
    'a2, 'a3, 'a4, 'a5) action -> ('a6, fn_tc_error) result -> ('a6, ('a1,
    'a2, 'a3) error) result **)

let lift_fn2_tc_result r0 sigma sig1 tau1 sig2 tau2 pos1 e1 pos2 e2 r1 =
  result_map_failure (fun pat ->
    let (side, err) = pat in
    (match side with
     | Arg1 -> lift_basic_error_message r0 sigma pos1 sig1 tau1 e1 err
     | Arg2 -> lift_basic_error_message r0 sigma pos2 sig2 tau2 e2 err)) r1

(** val mkerror :
    'a1 -> ('a3, 'a2) error_message -> 'a4 -> ('a1, 'a3, 'a2) error **)

let mkerror pos msg _ =
  { epos = pos; emsg = msg }

(** val cast_action' :
    ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a1 -> 'a3 tsig -> type0
    -> type0 -> ('a1, 'a3, 'a2, 'a4, 'a5) action -> ('a3, 'a2) error_message
    -> (('a1, 'a3, 'a2, 'a4, 'a5) action, ('a1, 'a3, 'a2) error) result **)

let cast_action' _ _ pos _ tau1 tau2 e emsg0 =
  let s = eqDec_type.eq_dec tau1 tau2 in
  if s then Success e else Failure (mkerror pos emsg0 e)

(** val cast_action :
    ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a1 -> 'a3 tsig -> type0
    -> type0 -> ('a1, 'a3, 'a2, 'a4, 'a5) action -> (('a1, 'a3, 'a2, 'a4,
    'a5) action, ('a1, 'a3, 'a2) error) result **)

let cast_action r0 sigma pos sig0 tau1 tau2 e =
  cast_action' r0 sigma pos sig0 tau1 tau2 e (BasicError (TypeMismatch (tau1,
    tau2)))

(** val actpos : 'a1 -> ('a1, 'a3, 'a2, 'a4, 'a5) uaction -> 'a1 **)

let actpos pos = function
| UAPos (p, _) -> p
| _ -> pos

(** val assert_argtypes' :
    ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a3 tsig -> 'a6 -> int ->
    'a2 -> 'a1 -> 'a3 tsig -> ('a1 * (type0, ('a1, 'a3, 'a2, 'a4, 'a5)
    action) sigT) list -> (('a3 * type0, ('a1, 'a3, 'a2, 'a4, 'a5) action)
    context, ('a1, 'a3, 'a2) error) result **)

let rec assert_argtypes' r0 sigma sig0 src nexpected fn_name pos args_desc args =
  match args_desc with
  | [] ->
    (match args with
     | [] -> Success CtxEmpty
     | _ :: _ ->
       Failure
         (mkerror pos (TooManyArguments (fn_name, nexpected, (length args)))
           src))
  | p :: fn_sig ->
    let (name1, tau1) = p in
    (match args with
     | [] ->
       Failure
         (mkerror pos (TooFewArguments (fn_name, nexpected,
           (length args_desc))) src)
     | p0 :: args0 ->
       let (pos1, arg1) = p0 in
       (match cast_action r0 sigma pos1 sig0 (projT1 arg1) tau1 (projT2 arg1) with
        | Success arg2 ->
          (match assert_argtypes' r0 sigma sig0 src nexpected fn_name pos
                   fn_sig args0 with
           | Success ctx ->
             Success (CtxCons (fn_sig, (name1, tau1), arg2, ctx))
           | Failure f -> Failure f)
        | Failure f -> Failure f))

(** val assert_argtypes :
    ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a3 tsig -> 'a6 -> 'a2 ->
    'a1 -> 'a3 tsig -> ('a1 * (type0, ('a1, 'a3, 'a2, 'a4, 'a5) action) sigT)
    list -> (('a3 * type0, ('a1, 'a3, 'a2, 'a4, 'a5) action) context, ('a1,
    'a3, 'a2) error) result **)

let assert_argtypes r0 sigma sig0 src fn_name pos args_desc args =
  assert_argtypes' r0 sigma sig0 src (length args_desc) fn_name pos args_desc
    args

(** val type_action :
    'a3 eqDec -> ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a1 -> 'a3
    tsig -> ('a1, 'a3, 'a2, 'a4, 'a5) uaction -> ((type0, ('a1, 'a3, 'a2,
    'a4, 'a5) action) sigT, ('a1, 'a3, 'a2) error) result **)

let rec type_action var_t_eq_dec r0 sigma pos sig0 e = match e with
| UError err -> Failure err
| UFail tau -> Success (ExistT (tau, (Fail (sig0, tau))))
| UVar var ->
  (match opt_result (assoc var_t_eq_dec var sig0)
           (mkerror pos (UnboundVariable var) e) with
   | Success tau_m ->
     Success (ExistT ((projT1 tau_m), (Var (sig0, var, (projT1 tau_m),
       (projT2 tau_m)))))
   | Failure f -> Failure f)
| UConst (tau, cst) -> Success (ExistT (tau, (Const (sig0, tau, cst))))
| UAssign (var, ex) ->
  (match opt_result (assoc var_t_eq_dec var sig0)
           (mkerror pos (UnboundVariable var) e) with
   | Success tau_m ->
     (match type_action var_t_eq_dec r0 sigma pos sig0 ex with
      | Success ex' ->
        (match cast_action r0 sigma (actpos pos ex) sig0 (projT1 ex')
                 (projT1 tau_m) (projT2 ex') with
         | Success ex'0 ->
           Success (ExistT ((Bits_t 0), (Assign (sig0, var, (projT1 tau_m),
             (projT2 tau_m), ex'0))))
         | Failure f -> Failure f)
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| USeq (r1, r2) ->
  (match type_action var_t_eq_dec r0 sigma pos sig0 r1 with
   | Success r1' ->
     (match cast_action r0 sigma (actpos pos r1) sig0 (projT1 r1') (Bits_t 0)
              (projT2 r1') with
      | Success r1'0 ->
        (match type_action var_t_eq_dec r0 sigma pos sig0 r2 with
         | Success r2' ->
           Success (ExistT ((projT1 r2'), (Seq (sig0, (projT1 r2'), r1'0,
             (projT2 r2')))))
         | Failure f -> Failure f)
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UBind (v, ex, body) ->
  (match type_action var_t_eq_dec r0 sigma pos sig0 ex with
   | Success ex0 ->
     (match type_action var_t_eq_dec r0 sigma pos ((v, (projT1 ex0)) :: sig0)
              body with
      | Success body0 ->
        Success (ExistT ((projT1 body0), (Bind (sig0, (projT1 ex0),
          (projT1 body0), v, (projT2 ex0), (projT2 body0)))))
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UIf (cond, tbranch, fbranch) ->
  (match type_action var_t_eq_dec r0 sigma pos sig0 cond with
   | Success cond' ->
     (match cast_action r0 sigma (actpos pos cond) sig0 (projT1 cond')
              (Bits_t (Pervasives.succ 0)) (projT2 cond') with
      | Success cond'0 ->
        (match type_action var_t_eq_dec r0 sigma pos sig0 tbranch with
         | Success tbranch' ->
           (match type_action var_t_eq_dec r0 sigma pos sig0 fbranch with
            | Success fbranch' ->
              (match cast_action r0 sigma (actpos pos fbranch) sig0
                       (projT1 fbranch') (projT1 tbranch') (projT2 fbranch') with
               | Success fbranch'0 ->
                 Success (ExistT ((projT1 tbranch'), (If (sig0,
                   (projT1 tbranch'), cond'0, (projT2 tbranch'), fbranch'0))))
               | Failure f -> Failure f)
            | Failure f -> Failure f)
         | Failure f -> Failure f)
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| URead (port0, idx) -> Success (ExistT ((r0 idx), (Read (sig0, port0, idx))))
| UWrite (port0, idx, value) ->
  (match type_action var_t_eq_dec r0 sigma pos sig0 value with
   | Success value' ->
     (match cast_action r0 sigma (actpos pos value) sig0 (projT1 value')
              (r0 idx) (projT2 value') with
      | Success value'0 ->
        Success (ExistT ((Bits_t 0), (Write (sig0, port0, idx, value'0))))
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UUnop (fn, arg1) ->
  let pos1 = actpos pos arg1 in
  (match type_action var_t_eq_dec r0 sigma pos sig0 arg1 with
   | Success arg1' ->
     (match lift_fn1_tc_result r0 sigma sig0 (projT1 arg1') pos1
              (projT2 arg1') (PrimTypeInference.tc1 fn (projT1 arg1')) with
      | Success fn0 ->
        (match cast_action r0 sigma pos1 sig0 (projT1 arg1')
                 (vect_hd 0
                   (Obj.magic (PrimSignatures.coq_Sigma1 fn0).argSigs))
                 (projT2 arg1') with
         | Success arg1'0 ->
           Success (ExistT ((PrimSignatures.coq_Sigma1 fn0).retSig, (Unop
             (sig0, fn0, arg1'0))))
         | Failure f -> Failure f)
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UBinop (fn, arg1, arg2) ->
  let pos1 = actpos pos arg1 in
  let pos2 = actpos pos arg2 in
  (match type_action var_t_eq_dec r0 sigma pos sig0 arg1 with
   | Success arg1' ->
     (match type_action var_t_eq_dec r0 sigma pos sig0 arg2 with
      | Success arg2' ->
        (match lift_fn2_tc_result r0 sigma sig0 (projT1 arg1') sig0
                 (projT1 arg2') pos1 (projT2 arg1') pos2 (projT2 arg2')
                 (PrimTypeInference.tc2 fn (projT1 arg1') (projT1 arg2')) with
         | Success fn0 ->
           (match cast_action r0 sigma pos1 sig0 (projT1 arg1')
                    (vect_hd (Pervasives.succ 0)
                      (Obj.magic (PrimSignatures.coq_Sigma2 fn0).argSigs))
                    (projT2 arg1') with
            | Success arg1'0 ->
              (match cast_action r0 sigma pos2 sig0 (projT1 arg2')
                       (vect_hd 0
                         (Obj.magic vect_tl (Pervasives.succ 0)
                           (PrimSignatures.coq_Sigma2 fn0).argSigs))
                       (projT2 arg2') with
               | Success arg2'0 ->
                 Success (ExistT ((PrimSignatures.coq_Sigma2 fn0).retSig,
                   (Binop (sig0, fn0, arg1'0, arg2'0))))
               | Failure f -> Failure f)
            | Failure f -> Failure f)
         | Failure f -> Failure f)
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UExternalCall (fn, arg1) ->
  let pos1 = actpos pos arg1 in
  (match type_action var_t_eq_dec r0 sigma pos1 sig0 arg1 with
   | Success arg1' ->
     (match cast_action r0 sigma pos1 sig0 (projT1 arg1')
              (vect_hd 0 (Obj.magic (sigma fn).argSigs)) (projT2 arg1') with
      | Success arg1'0 ->
        Success (ExistT ((sigma fn).retSig, (ExternalCall (sig0, fn,
          arg1'0))))
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UInternalCall (fn, args) ->
  (match result_list_map (type_action var_t_eq_dec r0 sigma pos sig0) args with
   | Success tc_args ->
     let arg_positions = map (actpos pos) args in
     let tc_args_w_pos = combine arg_positions tc_args in
     (match assert_argtypes r0 sigma sig0 e fn.int_name pos
              (rev fn.int_argspec) (rev tc_args_w_pos) with
      | Success args_ctx ->
        (match type_action var_t_eq_dec r0 sigma (actpos pos fn.int_body)
                 (rev fn.int_argspec) fn.int_body with
         | Success fn_body' ->
           (match cast_action r0 sigma (actpos pos fn.int_body)
                    (rev fn.int_argspec) (projT1 fn_body') fn.int_retSig
                    (projT2 fn_body') with
            | Success fn_body'0 ->
              Success (ExistT (fn.int_retSig, (InternalCall (sig0,
                fn.int_retSig, fn.int_name, fn.int_argspec, args_ctx,
                fn_body'0))))
            | Failure f -> Failure f)
         | Failure f -> Failure f)
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UAPos (pos0, e0) ->
  (match type_action var_t_eq_dec r0 sigma pos0 sig0 e0 with
   | Success e1 ->
     Success (ExistT ((projT1 e1), (APos (sig0, (projT1 e1), pos0,
       (projT2 e1)))))
   | Failure f -> Failure f)
| USugar _ -> Failure (mkerror pos SugaredConstructorInAst e)

(** val tc_action :
    'a3 eqDec -> ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a1 -> 'a3
    tsig -> type0 -> ('a1, 'a3, 'a2, 'a4, 'a5) uaction -> (('a1, 'a3, 'a2,
    'a4, 'a5) action, ('a1, 'a3, 'a2) error) result **)

let tc_action var_t_eq_dec r0 sigma pos sig0 expected_tau e =
  match type_action var_t_eq_dec r0 sigma pos sig0 e with
  | Success a ->
    cast_action r0 sigma pos sig0 (projT1 a) expected_tau (projT2 a)
  | Failure f -> Failure f

type ext_fn_rtl_spec = { efr_name : char list; efr_internal : bool }

type ext_fn_sim_spec = { efs_name : char list; efs_method : bool }

(** val empty_Sigma : __ -> externalSignature **)

let empty_Sigma _ =
  assert false (* absurd case *)

(** val empty_ext_fn_props : __ -> 'a1 **)

let empty_ext_fn_props _ =
  assert false (* absurd case *)

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

type 'pos_t dummyPos = { dummy_pos : 'pos_t }

(** val dummyPos_unit : unit dummyPos **)

let dummyPos_unit =
  { dummy_pos = () }

type pos_t = unit

type var_t = char list

type fn_name_t = char list

module ProducerConsumer =
 struct
  (** val r_sz : int **)

  let r_sz =
    pow2 (Pervasives.succ (Pervasives.succ 0))

  type reg_t =
  | Coq_producer_counter
  | Coq_queue_empty
  | Coq_queue_data
  | Coq_output

  (** val coq_R : reg_t -> type0 **)

  let coq_R = function
  | Coq_queue_empty -> Bits_t (Pervasives.succ 0)
  | _ -> Bits_t r_sz

  (** val r : reg_t -> type_denote **)

  let r = function
  | Coq_queue_empty -> Bits.one (Pervasives.succ 0)
  | _ -> Bits.zero r_sz

  type rule_name_t =
  | Coq_produce
  | Coq_consume

  (** val rules :
      rule_name_t -> (pos_t, var_t, fn_name_t, reg_t, __) action **)

  let rules = function
  | Coq_produce ->
    extract_success
      (let desugared =
         desugar_action dummyPos_unit.dummy_pos (UBind (('q'::[]), (URead
           (P0, Coq_queue_empty)), (UIf ((UVar ('q'::[])), (UBind (('v'::[]),
           (URead (P0, Coq_producer_counter)), (USeq ((USeq ((UWrite (P0,
           Coq_queue_data, (UVar ('v'::[])))), (UWrite (P0,
           Coq_producer_counter, (UBinop ((PrimUntyped.UBits2
           PrimUntyped.UPlus), (UVar ('v'::[])), (USugar (UConstBits
           ((Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ 0)))),
           (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
             (Pervasives.succ 0))) true
             (vect_cons (Pervasives.succ (Pervasives.succ 0)) false
               (Obj.magic vect_cons (Pervasives.succ 0) false
                 (vect_cons 0 false (Obj.magic __)))))))))))))), (UWrite (P0,
           Coq_queue_empty, (USugar (UConstBits ((Pervasives.succ 0),
           (Obj.magic vect_cons 0 true __)))))))))), (UFail (Bits_t 0))))))
       in
       tc_action eqDec_string coq_R empty_Sigma dummyPos_unit.dummy_pos []
         (Bits_t 0) desugared)
  | Coq_consume ->
    extract_success
      (let desugared =
         desugar_action dummyPos_unit.dummy_pos (UBind (('q'::[]), (URead
           (P1, Coq_queue_empty)), (UIf ((UUnop ((PrimUntyped.UBits1
           PrimUntyped.UNot), (UVar ('q'::[])))), (UBind (('v'::[]), (URead
           (P1, Coq_queue_data)), (USeq ((UWrite (P1, Coq_queue_empty,
           (USugar (UConstBits ((Pervasives.succ 0),
           (Obj.magic vect_cons 0 false __)))))), (UWrite (P1, Coq_output,
           (UVar ('v'::[])))))))), (UFail (Bits_t 0))))))
       in
       tc_action eqDec_string coq_R empty_Sigma dummyPos_unit.dummy_pos []
         (Bits_t 0) desugared)

  (** val pc_scheduler : (pos_t, rule_name_t) scheduler **)

  let pc_scheduler =
    Cons (Coq_produce, (Cons (Coq_consume, Done)))

  (** val coq_external : rule_name_t -> bool **)

  let coq_external _ =
    false

  (** val package : interop_package_t **)

  let package =
    { ip_koika = { koika_var_names = show_string; koika_fn_names =
      show_string; koika_reg_names = { show0 = (fun h ->
      match Obj.magic h with
      | Coq_producer_counter ->
        'p'::('r'::('o'::('d'::('u'::('c'::('e'::('r'::('_'::('c'::('o'::('u'::('n'::('t'::('e'::('r'::[])))))))))))))))
      | Coq_queue_empty ->
        'q'::('u'::('e'::('u'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::[]))))))))))
      | Coq_queue_data ->
        'q'::('u'::('e'::('u'::('e'::('_'::('d'::('a'::('t'::('a'::[])))))))))
      | Coq_output -> 'o'::('u'::('t'::('p'::('u'::('t'::[])))))) };
      koika_reg_types = (Obj.magic coq_R); koika_reg_init = (fun reg ->
      r (Obj.magic reg)); koika_reg_finite = { finite_index = (fun h ->
      match Obj.magic h with
      | Coq_producer_counter -> 0
      | Coq_queue_empty -> Pervasives.succ 0
      | Coq_queue_data -> Pervasives.succ (Pervasives.succ 0)
      | Coq_output -> Pervasives.succ (Pervasives.succ (Pervasives.succ 0)));
      finite_elements =
      ((Obj.magic Coq_producer_counter) :: ((Obj.magic Coq_queue_empty) :: (
      (Obj.magic Coq_queue_data) :: ((Obj.magic Coq_output) :: [])))) };
      koika_ext_fn_types = (Obj.magic empty_Sigma); koika_rules =
      (Obj.magic rules); koika_rule_external = (Obj.magic coq_external);
      koika_rule_names = { show0 = (fun h ->
      match Obj.magic h with
      | Coq_produce -> 'p'::('r'::('o'::('d'::('u'::('c'::('e'::[]))))))
      | Coq_consume -> 'c'::('o'::('n'::('s'::('u'::('m'::('e'::[]))))))) };
      koika_scheduler = (Obj.magic pc_scheduler); koika_module_name =
      ('v'::('e'::('c'::('t'::('o'::('r'::[])))))) }; ip_verilog =
      { vp_ext_fn_specs = (Obj.magic empty_ext_fn_props) }; ip_sim =
      { sp_ext_fn_specs = (Obj.magic empty_ext_fn_props); sp_prelude =
      None } }
 end

(** val prog : unit **)

let prog =
  Backends.register ProducerConsumer.package
