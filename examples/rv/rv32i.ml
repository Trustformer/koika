
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

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

(** val id : 'a1 -> 'a1 **)

let id x =
  x

type 'a sig0 =
| Exist of 'a

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

module Coq__1 = struct
 (** val add : int -> int -> int **)let rec add = (+)
end
include Coq__1

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Pervasives.max 0 (n-m)

module Nat =
 struct
  (** val pred : int -> int **)

  let pred n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n0)
      (fun u -> u)
      n0

  (** val add : int -> int -> int **)

  let rec add n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Pervasives.succ (add p m))
      n0

  (** val mul : int -> int -> int **)

  let rec mul n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n0

  (** val sub : int -> int -> int **)

  let rec sub n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n0)
      (fun k ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n0)
        (fun l -> sub k l)
        m)
      n0

  (** val compare : int -> int -> comparison **)

  let rec compare = fun n m -> if n=m then Eq else if n<m then Lt else Gt

  (** val max : int -> int -> int **)

  let rec max n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n0)
        (fun m' -> Pervasives.succ (max n' m'))
        m)
      n0

  (** val pow : int -> int -> int **)

  let rec pow n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Pervasives.succ 0)
      (fun m0 -> mul n0 (pow n0 m0))
      m

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q u =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (q, u))
      (fun x' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> divmod x' y (Pervasives.succ q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val div : int -> int -> int **)

  let div x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> y)
      (fun y' -> fst (divmod x y' 0 y'))
      y

  (** val modulo : int -> int -> int **)

  let modulo x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> y)
      (fun y' -> sub y' (snd (divmod x y' 0 y')))
      y

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

  let log2 n0 =
    log2_iter (pred n0) 0 (Pervasives.succ 0) 0

  (** val log2_up : int -> int **)

  let log2_up a =
    match compare (Pervasives.succ 0) a with
    | Lt -> Pervasives.succ (log2 (pred a))
    | _ -> 0
 end

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
| [] -> false
| y :: l0 -> let s = h y a in if s then true else in_dec h a l0

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

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| [] -> None
| x :: tl -> if f x then Some x else find f tl

(** val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let rec combine l l' =
  match l with
  | [] -> []
  | x :: tl ->
    (match l' with
     | [] -> []
     | y :: tl' -> (x, y) :: (combine tl tl'))

(** val skipn : int -> 'a1 list -> 'a1 list **)

let rec skipn n0 l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n1 -> match l with
               | [] -> []
               | _ :: l0 -> skipn n1 l0)
    n0

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Pervasives.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : int -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Pervasives.succ 0)

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n0
 end

module N =
 struct
  (** val zero : int **)

  let zero =
    0

  (** val add : int -> int -> int **)

  let add = (+)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val to_nat : int -> int **)

  let to_nat a =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> Pos.to_nat p)
      a

  (** val of_nat : int -> int **)

  let of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' -> (Pos.of_succ_nat n'))
      n0
 end

(** val le_gt_dec : int -> int -> bool **)

let le_gt_dec =
  (<=)



(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

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

(** val index_of_nat_lt : int -> int -> index **)

let index_of_nat_lt sz0 n0 =
  let o = index_of_nat sz0 n0 in
  (match o with
   | Some idx -> idx
   | None -> assert false (* absurd case *))

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

let rec vect_const sz0 t =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic __)
    (fun sz1 -> Obj.magic vect_cons sz1 t (vect_const sz1 t))
    sz0

(** val vect_app : int -> int -> 'a1 vect -> 'a1 vect -> 'a1 vect **)

let rec vect_app sz1 sz2 v1 v2 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic v2)
    (fun sz3 ->
    Obj.magic vect_cons (add sz3 sz2) (vect_hd sz3 (Obj.magic v1))
      (vect_app sz3 sz2 (vect_tl sz3 (Obj.magic v1)) v2))
    sz1

(** val vect_split : int -> int -> 'a1 vect -> 'a1 vect * 'a1 vect **)

let rec vect_split sz1 sz2 v =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ((Obj.magic __), v))
    (fun sz3 ->
    let (v1, v2) =
      vect_split sz3 sz2
        (vect_tl
          (let rec add0 n0 m =
             (fun fO fS n -> if n=0 then fO () else fS (n-1))
               (fun _ -> m)
               (fun p -> Pervasives.succ (add0 p m))
               n0
           in add0 sz3 sz2) (Obj.magic v))
    in
    ((Obj.magic vect_cons sz3
       (vect_hd
         (let rec add0 n0 m =
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> m)
              (fun p -> Pervasives.succ (add0 p m))
              n0
          in add0 sz3 sz2) (Obj.magic v)) v1), v2))
    sz1

(** val vect_nth : int -> 'a1 vect -> index -> 'a1 **)

let rec vect_nth n0 v idx =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> assert false (* absurd case *))
    (fun n1 ->
    (fun fthisone fanotherone n -> if n = 0 then fthisone () else fanotherone (n - 1))
      (fun _ -> vect_hd n1 (Obj.magic v))
      (fun idx0 -> vect_nth n1 (vect_tl n1 (Obj.magic v)) idx0)
      (Obj.magic idx))
    n0

(** val vect_map : int -> ('a1 -> 'a2) -> 'a1 vect -> 'a2 vect **)

let rec vect_map n0 f v =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic __ v)
    (fun n1 ->
    Obj.magic vect_cons n1 (f (vect_hd n1 (Obj.magic v)))
      (vect_map n1 f (vect_tl n1 (Obj.magic v))))
    n0

(** val vect_fold_left :
    int -> ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 vect -> 'a1 **)

let rec vect_fold_left n0 f a0 v =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic a0)
    (fun n1 ->
    f (vect_fold_left n1 f a0 (vect_tl n1 (Obj.magic v)))
      (vect_hd n1 (Obj.magic v)))
    n0

(** val vect_find_index : int -> ('a1 -> bool) -> 'a1 vect -> index option **)

let rec vect_find_index sz0 f v =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic None)
    (fun n0 ->
    if f (vect_hd n0 (Obj.magic v))
    then Some (Obj.magic 0)
    else (match vect_find_index n0 f (vect_tl n0 (Obj.magic v)) with
          | Some idx -> Some (Obj.magic (Pervasives.succ idx))
          | None -> None))
    sz0

(** val vect_index : int -> 'a1 eqDec -> 'a1 -> 'a1 vect -> index option **)

let vect_index sz0 eQ k v =
  vect_find_index sz0 (fun t -> beq_dec eQ t k) v

(** val vect_to_list : int -> 'a1 vect -> 'a1 list **)

let vect_to_list n0 v =
  vect_fold_left n0 (fun acc t -> t :: acc) [] v

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

let rec eqDec_vect n0 h =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic eqDec_vect_nil h)
    (fun n1 -> Obj.magic eqDec_vect_cons h (eqDec_vect n1 h))
    n0

(** val pow2 : int -> int **)

let pow2 n0 =
  Pervasives.succ (pred (Nat.pow (Pervasives.succ (Pervasives.succ 0)) n0))

module Bits =
 struct
  (** val rmul : int -> int -> int **)

  let rec rmul n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add (rmul p m) m)
      n0

  (** val splitn : int -> int -> bool vect -> bool vect vect **)

  let rec splitn n0 sz0 bs =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Obj.magic __ bs)
      (fun n1 ->
      let (rest, hd) =
        vect_split
          (let rec rmul0 n2 m =
             (fun fO fS n -> if n=0 then fO () else fS (n-1))
               (fun _ -> 0)
               (fun p -> add (rmul0 p m) m)
               n2
           in rmul0 n1 sz0) sz0 bs
      in
      Obj.magic vect_cons n1 hd (splitn n1 sz0 rest))
      n0

  (** val appn : int -> int -> bool vect vect -> bool vect **)

  let rec appn n0 sz0 bss =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Obj.magic __ bss)
      (fun n1 ->
      let x = vect_hd n1 (Obj.magic bss) in
      let y = appn n1 sz0 (vect_tl n1 (Obj.magic bss)) in
      vect_app (rmul n1 sz0) sz0 y x)
      n0

  (** val neg : int -> bool vect -> bool vect **)

  let neg sz0 b =
    vect_map sz0 negb b

  (** val to_N : int -> bool vect -> int **)

  let rec to_N sz0 bs =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Obj.magic 0)
      (fun n0 ->
      N.add (if vect_hd n0 (Obj.magic bs) then 1 else 0)
        (N.mul ((fun p->2*p) 1) (to_N n0 (vect_tl n0 (Obj.magic bs)))))
      sz0

  (** val to_nat : int -> bool vect -> int **)

  let to_nat sz0 bs =
    N.to_nat (to_N sz0 bs)

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

  let of_N sz0 n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> vect_const sz0 false)
      (fun p -> of_positive sz0 p)
      n0

  (** val of_nat : int -> int -> bool vect **)

  let of_nat sz0 n0 =
    of_N sz0 (N.of_nat n0)

  (** val of_index : int -> int -> index -> bool vect **)

  let of_index sz0 n0 idx =
    of_nat sz0 (index_to_nat n0 idx)

  (** val to_index_safe : int -> bool vect -> index **)

  let to_index_safe sz0 bs =
    index_of_nat_lt (pow2 sz0) (to_nat sz0 bs)

  (** val zero : int -> bool vect **)

  let zero sz0 =
    of_N sz0 N.zero
 end

type 't finiteType = { finite_index : ('t -> int); finite_elements : 't list }

type 'a show = { show0 : ('a -> char list) }

module Show_nat =
 struct
  (** val string_of_base10_digit : int sig0 -> char list **)

  let string_of_base10_digit = function
  | Exist n1 ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> '0'::[])
       (fun n2 ->
       (fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ -> '1'::[])
         (fun n3 ->
         (fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ -> '2'::[])
           (fun n4 ->
           (fun fO fS n -> if n=0 then fO () else fS (n-1))
             (fun _ -> '3'::[])
             (fun n5 ->
             (fun fO fS n -> if n=0 then fO () else fS (n-1))
               (fun _ -> '4'::[])
               (fun n6 ->
               (fun fO fS n -> if n=0 then fO () else fS (n-1))
                 (fun _ -> '5'::[])
                 (fun n7 ->
                 (fun fO fS n -> if n=0 then fO () else fS (n-1))
                   (fun _ -> '6'::[])
                   (fun n8 ->
                   (fun fO fS n -> if n=0 then fO () else fS (n-1))
                     (fun _ -> '7'::[])
                     (fun n9 ->
                     (fun fO fS n -> if n=0 then fO () else fS (n-1))
                       (fun _ -> '8'::[])
                       (fun n10 ->
                       (fun fO fS n -> if n=0 then fO () else fS (n-1))
                         (fun _ -> '9'::[])
                         (fun _ -> assert false (* absurd case *))
                         n10)
                       n9)
                     n8)
                   n7)
                 n6)
               n5)
             n4)
           n3)
         n2)
       n1)

  (** val string_of_nat_rec : int -> int -> char list **)

  let rec string_of_nat_rec fuel n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> [])
      (fun fuel0 ->
      if (<) n0 (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ 0))))))))))
      then string_of_base10_digit (Exist n0)
      else append
             (string_of_nat_rec fuel0
               (Nat.div n0 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ 0))))))))))))
             (string_of_nat_rec fuel0
               (Nat.modulo n0 (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ 0)))))))))))))
      fuel

  (** val string_of_nat : int -> char list **)

  let string_of_nat n0 =
    string_of_nat_rec (Pervasives.succ n0) n0
 end

(** val show_nat : int show **)

let show_nat =
  { show0 = Show_nat.string_of_nat }

(** val show_string : char list show **)

let show_string =
  { show0 = (fun x -> x) }

(** val eqDec_FiniteType : 'a1 finiteType -> 'a1 eqDec **)

let eqDec_FiniteType fT =
  { eq_dec = (fun t1 t2 -> (=) (fT.finite_index t1) (fT.finite_index t2)) }

(** val list_sum' : int -> int list -> int **)

let list_sum' n0 l =
  fold_right (fun x acc -> add acc x) n0 l

(** val list_sum : int list -> int **)

let list_sum l =
  list_sum' 0 l

(** val dedup : 'a1 eqDec -> 'a1 list -> 'a1 list -> 'a1 list **)

let rec dedup eQ acc = function
| [] -> acc
| a :: l0 ->
  let already_seen = in_dec eQ.eq_dec a acc in
  let acc0 = if already_seen then acc else a :: acc in dedup eQ acc0 l0

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

(** val mdestruct : 'a1 list -> 'a1 -> 'a1 member -> __ **)

let mdestruct _ _ = function
| MemberHd (_, _) -> Obj.magic (Inl (ExistT (__, __)))
| MemberTl (_, _, _, m0) -> Obj.magic (Inr (ExistT (m0, __)))

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

(** val member_map :
    ('a1 -> 'a2) -> 'a1 -> 'a1 list -> 'a1 member -> 'a2 member **)

let rec member_map f _ _ = function
| MemberHd (k, sig1) -> MemberHd ((f k), (map f sig1))
| MemberTl (k, k', sig1, m') ->
  MemberTl ((f k), (f k'), (map f sig1), (member_map f k sig1 m'))

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

(** val mprefix : 'a1 list -> 'a1 list -> 'a1 -> 'a1 member -> 'a1 member **)

let rec mprefix prefix sig1 k m =
  match prefix with
  | [] -> m
  | k' :: prefix0 ->
    MemberTl (k, k', (app prefix0 sig1), (mprefix prefix0 sig1 k m))

(** val minfix :
    'a1 list -> 'a1 list -> 'a1 list -> 'a1 -> 'a1 member -> 'a1 member **)

let rec minfix infix sig1 sig' k m =
  match sig1 with
  | [] -> mprefix infix (app [] sig') k m
  | k' :: sig2 ->
    let y = mdestruct (app (k' :: sig2) sig') k m in
    (match Obj.magic y with
     | Inl _ -> MemberHd (k, (app sig2 (app infix sig')))
     | Inr s ->
       let ExistT (m', _) = s in
       MemberTl (k, k', (app sig2 (app infix sig')),
       (minfix infix sig2 sig' k m')))

(** val all_indices : int -> index vect **)

let rec all_indices bound =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic __)
    (fun bound0 ->
    Obj.magic vect_cons bound0 0
      (vect_map bound0 (fun x -> Pervasives.succ x) (all_indices bound0)))
    bound

(** val finiteType_index : int -> index finiteType **)

let finiteType_index n0 =
  { finite_index = (index_to_nat n0); finite_elements =
    (vect_to_list n0 (all_indices n0)) }

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

(** val show_index : int -> index show **)

let show_index n0 =
  { show0 = (fun x -> show_nat.show0 (index_to_nat n0 x)) }

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
| Enum_t sig1 -> Kind_enum (Some sig1)
| Struct_t sig1 -> Kind_struct (Some sig1)
| Array_t sig1 -> Kind_array (Some sig1)

(** val struct_fields_sz' :
    (type0 -> int) -> (char list * type0) list -> int **)

let struct_fields_sz' type_sz0 fields =
  list_sum (map (fun nm_tau -> type_sz0 (snd nm_tau)) fields)

(** val type_sz : type0 -> int **)

let rec type_sz = function
| Bits_t sz0 -> sz0
| Enum_t sig1 -> sig1.enum_bitsize
| Struct_t sig1 -> struct_fields_sz' type_sz sig1.struct_fields
| Array_t sig1 -> Bits.rmul sig1.array_len (type_sz sig1.array_type)

type struct_index = index

(** val struct_sz : type0 struct_sig' -> int **)

let struct_sz sig1 =
  type_sz (Struct_t sig1)

(** val field_type : type0 struct_sig' -> index -> type0 **)

let field_type sig1 idx =
  snd (list_nth sig1.struct_fields idx)

(** val field_sz : type0 struct_sig' -> index -> int **)

let field_sz sig1 idx =
  type_sz (field_type sig1 idx)

(** val field_offset_right : type0 struct_sig' -> struct_index -> int **)

let field_offset_right sig1 idx =
  let next_fields =
    skipn (Pervasives.succ (index_to_nat (length sig1.struct_fields) idx))
      sig1.struct_fields
  in
  struct_fields_sz' type_sz next_fields

type array_index = index

(** val array_sz : type0 array_sig' -> int **)

let array_sz sig1 =
  type_sz (Array_t sig1)

(** val element_sz : type0 array_sig' -> int **)

let element_sz sig1 =
  type_sz sig1.array_type

(** val element_offset_right : type0 array_sig' -> array_index -> int **)

let element_offset_right sig1 idx =
  Bits.rmul
    (sub sig1.array_len (Pervasives.succ (index_to_nat sig1.array_len idx)))
    (element_sz sig1)

type port =
| P0
| P1

type type_denote = __

(** val bits_of_value : type0 -> type_denote -> bool vect **)

let rec bits_of_value tau x =
  let bits_of_struct_value =
    let rec bits_of_struct_value fields x0 =
      match fields with
      | [] -> Obj.magic __ x0
      | p :: fields0 ->
        let (nm, tau0) = p in
        let (x1, xs) = x0 in
        let x2 = bits_of_value (snd (nm, tau0)) x1 in
        let y = Obj.magic bits_of_struct_value fields0 xs in
        vect_app (struct_fields_sz' type_sz fields0)
          (type_sz (snd (nm, tau0))) y x2
    in bits_of_struct_value
  in
  (match tau with
   | Struct_t sig1 -> Obj.magic bits_of_struct_value sig1.struct_fields x
   | Array_t sig1 ->
     Bits.appn sig1.array_len (type_sz sig1.array_type)
       (vect_map sig1.array_len (bits_of_value sig1.array_type) x)
   | _ -> x)

(** val value_of_bits : type0 -> bool vect -> type_denote **)

let rec value_of_bits tau bs =
  let value_of_struct_bits =
    let rec value_of_struct_bits fields bs0 =
      match fields with
      | [] -> ()
      | p :: fields0 ->
        let (nm, tau0) = p in
        let splt =
          vect_split
            (let rec fold_right1 = function
             | [] -> 0
             | b :: t -> let acc = fold_right1 t in add acc b
             in fold_right1
                  (let rec map1 = function
                   | [] -> []
                   | a :: t -> (type_sz (snd a)) :: (map1 t)
                   in map1 fields0)) (type_sz (snd (nm, tau0)))
            (Obj.magic bs0)
        in
        let hd = value_of_bits (snd (nm, tau0)) (snd splt) in
        let tl = Obj.magic value_of_struct_bits fields0 (fst splt) in
        Obj.magic (hd, tl)
    in value_of_struct_bits
  in
  (match tau with
   | Struct_t sig1 -> Obj.magic value_of_struct_bits sig1.struct_fields bs
   | Array_t sig1 ->
     vect_map sig1.array_len (value_of_bits sig1.array_type)
       (Bits.splitn sig1.array_len
         (let rec type_sz0 = function
          | Bits_t sz0 -> sz0
          | Enum_t sig2 -> sig2.enum_bitsize
          | Struct_t sig2 -> struct_fields_sz' type_sz0 sig2.struct_fields
          | Array_t sig2 ->
            Bits.rmul sig2.array_len (type_sz0 sig2.array_type)
          in type_sz0 sig1.array_type) bs)
   | _ -> bs)

type 'argKind _Sig = { argSigs : 'argKind vect; retSig : 'argKind }

(** val cSig_of_Sig : int -> type0 _Sig -> int _Sig **)

let cSig_of_Sig n0 sig1 =
  { argSigs = (vect_map n0 type_sz sig1.argSigs); retSig =
    (type_sz sig1.retSig) }

(** val sig_of_CSig : int -> int _Sig -> type0 _Sig **)

let sig_of_CSig n0 sig1 =
  { argSigs = (vect_map n0 (fun x -> Bits_t x) sig1.argSigs); retSig =
    (Bits_t sig1.retSig) }

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

(** val map_intf_body :
    ('a3 -> 'a4) -> ('a1, 'a2, 'a3) internalFunction -> ('a1, 'a2, 'a4)
    internalFunction **)

let map_intf_body f fn =
  { int_name = fn.int_name; int_argspec = fn.int_argspec; int_retSig =
    fn.int_retSig; int_body = (f fn.int_body) }

type 'var_t arg_sig = { arg_name : 'var_t; arg_type : type0 }

(** val prod_of_argsig : 'a1 arg_sig -> 'a1 * type0 **)

let prod_of_argsig a =
  (a.arg_name, a.arg_type)

(** val type_id : type0 -> char list **)

let rec type_id = function
| Bits_t sz0 ->
  append ('b'::('i'::('t'::('s'::('_'::[]))))) (show_nat.show0 sz0)
| Enum_t sig1 -> sig1.enum_name
| Struct_t sig1 -> sig1.struct_name
| Array_t sig1 ->
  append ('a'::('r'::('r'::('a'::('y'::('_'::[]))))))
    (append (show_nat.show0 sig1.array_len)
      (append ('_'::[]) (type_id sig1.array_type)))

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

let rec ccreate sig1 f =
  match sig1 with
  | [] -> CtxEmpty
  | h :: t ->
    CtxCons (t, h, (f h (MemberHd (h, t))),
      (ccreate t (fun k m -> f k (MemberTl (k, h, t, m)))))

(** val cassoc :
    'a1 list -> 'a1 -> 'a1 member -> ('a1, 'a2) context -> 'a2 **)

let rec cassoc _ _ m ctx =
  match m with
  | MemberHd (k, sig1) -> chd k sig1 ctx
  | MemberTl (k, k', sig1, m0) -> cassoc sig1 k m0 (ctl k' sig1 ctx)

(** val creplace :
    'a1 list -> 'a1 -> 'a1 member -> 'a2 -> ('a1, 'a2) context -> ('a1, 'a2)
    context **)

let rec creplace _ _ m v ctx =
  match m with
  | MemberHd (k, sig1) -> CtxCons (sig1, k, v, (ctl k sig1 ctx))
  | MemberTl (k, k', sig1, m0) ->
    CtxCons (sig1, k', (chd k' sig1 ctx),
      (creplace sig1 k m0 v (ctl k' sig1 ctx)))

(** val cmap :
    ('a1 -> 'a2) -> ('a1 -> 'a3 -> 'a4) -> 'a1 list -> ('a1, 'a3) context ->
    ('a2, 'a4) context **)

let rec cmap fK fV _ = function
| CtxEmpty -> CtxEmpty
| CtxCons (sig1, k, v, ctx0) ->
  CtxCons ((map fK sig1), (fK k), (fV k v), (cmap fK fV sig1 ctx0))

type 'k env = { getenv : (__ -> __ -> 'k -> __);
                putenv : (__ -> __ -> 'k -> __ -> __);
                create : (__ -> ('k -> __) -> __); finite_keys : 'k finiteType }

type ('k, 'v) env_t = __

(** val getenv : 'a1 env -> ('a1, 'a2) env_t -> 'a1 -> 'a2 **)

let getenv e x k =
  Obj.magic e.getenv __ x k

(** val putenv :
    'a1 env -> ('a1, 'a2) env_t -> 'a1 -> 'a2 -> ('a1, 'a2) env_t **)

let putenv e x k x0 =
  Obj.magic e.putenv __ x k x0

(** val create : 'a1 env -> ('a1 -> 'a2) -> ('a1, 'a2) env_t **)

let create e fn =
  Obj.magic e.create __ fn

(** val map0 :
    'a1 env -> ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) env_t -> ('a1, 'a3) env_t **)

let map0 e fn ev1 =
  create e (fun k -> fn k (getenv e ev1 k))

(** val zip :
    'a1 env -> ('a1, 'a2) env_t -> ('a1, 'a3) env_t -> ('a1, 'a2 * 'a3) env_t **)

let zip e ev1 ev2 =
  create e (fun k -> ((getenv e ev1 k), (getenv e ev2 k)))

(** val map2 :
    'a1 env -> ('a1 -> 'a2 -> 'a3 -> 'a4) -> ('a1, 'a2) env_t -> ('a1, 'a3)
    env_t -> ('a1, 'a4) env_t **)

let map2 e fn ev1 ev2 =
  create e (fun k -> fn k (getenv e ev1 k) (getenv e ev2 k))

(** val fold_right0 :
    'a1 env -> ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) env_t -> 'a3 -> 'a3 **)

let fold_right0 e f ev t0 =
  fold_right (fun k t -> f k (getenv e ev k) t) t0
    e.finite_keys.finite_elements

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
     | Bits_t sz0 -> Success (Obj.magic sz0)
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

  let coq_GetElementBits sig1 idx =
    Slice ((array_sz sig1), (element_offset_right sig1 idx),
      (element_sz sig1))

  (** val coq_SubstElementBits : type0 array_sig' -> array_index -> fbits2 **)

  let coq_SubstElementBits sig1 idx =
    SliceSubst ((array_sz sig1), (element_offset_right sig1 idx),
      (element_sz sig1))

  (** val coq_GetFieldBits : type0 struct_sig' -> struct_index -> fbits1 **)

  let coq_GetFieldBits sig1 idx =
    Slice ((struct_sz sig1), (field_offset_right sig1 idx),
      (field_sz sig1 idx))

  (** val coq_SubstFieldBits : type0 struct_sig' -> struct_index -> fbits2 **)

  let coq_SubstFieldBits sig1 idx =
    SliceSubst ((struct_sz sig1), (field_offset_right sig1 idx),
      (field_sz sig1 idx))
 end

module PrimTypeInference =
 struct
  (** val find_field :
      type0 struct_sig' -> char list -> (index, fn_tc_error) result **)

  let find_field sig1 f =
    opt_result (list_assoc eqDec_string f sig1.struct_fields) (Arg1,
      (UnboundField (f, sig1)))

  (** val check_index :
      type0 array_sig' -> int -> (array_index, fn_tc_error) result **)

  let check_index sig1 pos =
    opt_result (index_of_nat sig1.array_len pos) (Arg1, (OutOfBounds (pos,
      sig1)))

  (** val tc1 :
      PrimUntyped.ufn1 -> type0 -> (PrimTyped.fn1, fn_tc_error) result **)

  let tc1 fn tau1 =
    match fn with
    | PrimUntyped.UDisplay fn0 ->
      (match fn0 with
       | PrimUntyped.UDisplayUtf8 ->
         (match assert_kind (Kind_array None) Arg1 tau1 with
          | Success sig1 ->
            Success (PrimTyped.Display (PrimTyped.DisplayUtf8
              (Obj.magic sig1).array_len))
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
          | Success sig1 ->
            (match find_field (Obj.magic sig1) f with
             | Success idx ->
               Success (PrimTyped.Struct1 ((Obj.magic sig1), idx))
             | Failure f0 -> Failure f0)
          | Failure f0 -> Failure f0)
       | PrimUntyped.UGetFieldBits (sig1, f) ->
         (match find_field sig1 f with
          | Success idx ->
            Success (PrimTyped.Bits1 (PrimTyped.coq_GetFieldBits sig1 idx))
          | Failure f0 -> Failure f0))
    | PrimUntyped.UArray1 fn0 ->
      (match fn0 with
       | PrimUntyped.UGetElement pos ->
         (match assert_kind (Kind_array None) Arg1 tau1 with
          | Success sig1 ->
            (match check_index (Obj.magic sig1) pos with
             | Success idx ->
               Success (PrimTyped.Array1 ((Obj.magic sig1), idx))
             | Failure f -> Failure f)
          | Failure f -> Failure f)
       | PrimUntyped.UGetElementBits (sig1, pos) ->
         (match check_index sig1 pos with
          | Success idx ->
            Success (PrimTyped.Bits1 (PrimTyped.coq_GetElementBits sig1 idx))
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
          | Success sig1 ->
            (match find_field (Obj.magic sig1) f with
             | Success idx ->
               Success (PrimTyped.Struct2 ((Obj.magic sig1), idx))
             | Failure f0 -> Failure f0)
          | Failure f0 -> Failure f0)
       | PrimUntyped.USubstFieldBits (sig1, f) ->
         (match find_field sig1 f with
          | Success idx ->
            Success (PrimTyped.Bits2 (PrimTyped.coq_SubstFieldBits sig1 idx))
          | Failure f0 -> Failure f0))
    | PrimUntyped.UArray2 fn0 ->
      (match fn0 with
       | PrimUntyped.USubstElement pos ->
         (match assert_kind (Kind_array None) Arg1 tau1 with
          | Success sig1 ->
            (match check_index (Obj.magic sig1) pos with
             | Success idx ->
               Success (PrimTyped.Array2 ((Obj.magic sig1), idx))
             | Failure f -> Failure f)
          | Failure f -> Failure f)
       | PrimUntyped.USubstElementBits (sig1, pos) ->
         (match check_index sig1 pos with
          | Success idx ->
            Success (PrimTyped.Bits2
              (PrimTyped.coq_SubstElementBits sig1 idx))
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
  | PrimTyped.Not sz0 ->
    { argSigs = (Obj.magic vect_cons 0 sz0 __); retSig = sz0 }
  | PrimTyped.SExt (sz0, width) ->
    { argSigs = (Obj.magic vect_cons 0 sz0 __); retSig = (Nat.max sz0 width) }
  | PrimTyped.ZExtL (sz0, width) ->
    { argSigs = (Obj.magic vect_cons 0 sz0 __); retSig = (Nat.max sz0 width) }
  | PrimTyped.ZExtR (sz0, width) ->
    { argSigs = (Obj.magic vect_cons 0 sz0 __); retSig = (Nat.max sz0 width) }
  | PrimTyped.Repeat (sz0, times) ->
    { argSigs = (Obj.magic vect_cons 0 sz0 __); retSig = (mul times sz0) }
  | PrimTyped.Slice (sz0, _, width) ->
    { argSigs = (Obj.magic vect_cons 0 sz0 __); retSig = width }
  | PrimTyped.Lowered fn0 ->
    (match fn0 with
     | PrimTyped.IgnoreBits sz0 ->
       { argSigs = (Obj.magic vect_cons 0 sz0 __); retSig = 0 }
     | PrimTyped.DisplayBits fn3 ->
       cSig_of_Sig (Pervasives.succ 0) (coq_DisplaySigma fn3))

  (** val coq_CSigma2 : PrimTyped.fbits2 -> int _Sig **)

  let coq_CSigma2 = function
  | PrimTyped.And sz0 ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz0
        (vect_cons 0 sz0 (Obj.magic __))); retSig = sz0 }
  | PrimTyped.Or sz0 ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz0
        (vect_cons 0 sz0 (Obj.magic __))); retSig = sz0 }
  | PrimTyped.Xor sz0 ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz0
        (vect_cons 0 sz0 (Obj.magic __))); retSig = sz0 }
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
  | PrimTyped.Sel sz0 ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz0
        (vect_cons 0 (Nat.log2_up sz0) (Obj.magic __))); retSig =
      (Pervasives.succ 0) }
  | PrimTyped.SliceSubst (sz0, _, width) ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz0
        (vect_cons 0 width (Obj.magic __))); retSig = sz0 }
  | PrimTyped.IndexedSlice (sz0, width) ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz0
        (vect_cons 0 (Nat.log2_up sz0) (Obj.magic __))); retSig = width }
  | PrimTyped.Plus sz0 ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz0
        (vect_cons 0 sz0 (Obj.magic __))); retSig = sz0 }
  | PrimTyped.Minus sz0 ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz0
        (vect_cons 0 sz0 (Obj.magic __))); retSig = sz0 }
  | PrimTyped.Mul (sz1, sz2) ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz1
        (vect_cons 0 sz2 (Obj.magic __))); retSig = (add sz1 sz2) }
  | PrimTyped.EqBits (sz0, _) ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz0
        (vect_cons 0 sz0 (Obj.magic __))); retSig = (Pervasives.succ 0) }
  | PrimTyped.Compare (_, _, sz0) ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) sz0
        (vect_cons 0 sz0 (Obj.magic __))); retSig = (Pervasives.succ 0) }
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
  | PrimTyped.Struct1 (sig1, idx) ->
    { argSigs = (Obj.magic vect_cons 0 (Struct_t sig1) __); retSig =
      (field_type sig1 idx) }
  | PrimTyped.Array1 (sig1, _) ->
    { argSigs = (Obj.magic vect_cons 0 (Array_t sig1) __); retSig =
      sig1.array_type }

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
  | PrimTyped.Struct2 (sig1, idx) ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) (Struct_t sig1)
        (vect_cons 0 (field_type sig1 idx) (Obj.magic __))); retSig =
      (Struct_t sig1) }
  | PrimTyped.Array2 (sig1, _) ->
    { argSigs =
      (Obj.magic vect_cons (Pervasives.succ 0) (Array_t sig1)
        (vect_cons 0 sig1.array_type (Obj.magic __))); retSig = (Array_t
      sig1) }
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

let ustruct_init sig1 fields =
  let empty = uinit (Struct_t sig1) in
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
  let (label, action1) = p in
  UIf ((UBinop ((PrimUntyped.UEq false), var, label)), action1,
  (uswitch var default branches0))

(** val uswitch_nodefault :
    ('a1, 'a2, 'a3, 'a4, 'a5) uaction -> int -> (('a1, 'a2, 'a3, 'a4, 'a5)
    uaction * ('a1, 'a2, 'a3, 'a4, 'a5) uaction, __) vect_cons_t -> ('a1,
    'a2, 'a3, 'a4, 'a5) uaction **)

let rec uswitch_nodefault var nb branches =
  let (label, action1) = vect_hd nb branches in
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> action1)
     (fun nb0 -> UIf ((UBinop ((PrimUntyped.UEq false), var, label)),
     action1,
     (Obj.magic uswitch_nodefault var nb0
       (vect_tl (Pervasives.succ nb0) branches))))
     nb)

(** val gen_branches :
    int -> int -> (index -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction) -> (('a1, 'a2,
    'a3, 'a4, 'a5) uaction * ('a1, 'a2, 'a3, 'a4, 'a5) uaction) vect **)

let gen_branches label_sz bound branch_bodies =
  let label_of_index = fun idx -> UConst ((Bits_t label_sz),
    (Bits.of_index label_sz bound idx))
  in
  vect_map bound (fun idx -> ((label_of_index idx), (branch_bodies idx)))
    (all_indices bound)

(** val uswitch_stateful :
    ('a1, 'a2, 'a3, 'a4, 'a5) uaction -> int -> (('a1, 'a2, 'a3, 'a4, 'a5)
    uaction * ('a1, 'a2, 'a3, 'a4, 'a5) uaction) vect -> ('a1, 'a2, 'a3, 'a4,
    'a5) uaction **)

let rec uswitch_stateful var nb branches =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic uskip)
    (fun nb0 ->
    let (label, action1) = vect_hd nb0 (Obj.magic branches) in
    USeq ((UIf ((UBinop ((PrimUntyped.UEq false), var, label)), action1,
    uskip)), (uswitch_stateful var nb0 (vect_tl nb0 (Obj.magic branches)))))
    nb

(** val muxtree :
    int -> int -> 'a2 -> int -> (bool vect -> ('a1, 'a2, 'a3, 'a4, 'a5)
    uaction) -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction **)

let rec muxtree var_logsz bit_idx var sz0 bodies =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic bodies __)
    (fun n0 ->
    let bidx = UConst ((Bits_t var_logsz), (Bits.of_nat var_logsz bit_idx)) in
    UIf ((UBinop ((PrimUntyped.UBits2 PrimUntyped.USel), (UVar var), bidx)),
    (muxtree var_logsz (Pervasives.succ bit_idx) var n0 (fun bs ->
      Obj.magic bodies (vect_cons n0 true bs))),
    (muxtree var_logsz (Pervasives.succ bit_idx) var n0 (fun bs ->
      Obj.magic bodies (vect_cons n0 false bs)))))
    sz0

(** val uCompleteMuxTree :
    int -> 'a2 -> (bool vect -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction) -> ('a1,
    'a2, 'a3, 'a4, 'a5) uaction **)

let uCompleteMuxTree sz0 var branch_bodies =
  muxtree (Nat.log2_up sz0) 0 var sz0 branch_bodies

(** val ortree :
    int -> (bool vect -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction) -> ('a1, 'a2,
    'a3, 'a4, 'a5) uaction **)

let rec ortree sz0 bodies =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic bodies __)
    (fun n0 -> UBinop ((PrimUntyped.UBits2 PrimUntyped.UOr),
    (ortree n0 (fun bs -> Obj.magic bodies (vect_cons n0 true bs))),
    (ortree n0 (fun bs -> Obj.magic bodies (vect_cons n0 false bs)))))
    sz0

(** val uCompleteOrTree :
    int -> int -> 'a2 -> (bool vect -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction) ->
    ('a1, 'a2, 'a3, 'a4, 'a5) uaction **)

let uCompleteOrTree sz0 nbits var branch_bodies =
  ortree sz0 (fun bs -> UIf ((UBinop ((PrimUntyped.UEq false), (UConst
    ((Bits_t sz0), bs)), (UVar var))), (branch_bodies bs), (UConst ((Bits_t
    nbits), (Bits.zero nbits)))))

type 'var_t switch_style =
| TreeSwitch
| OrTreeSwitch of int
| NestedSwitch
| SequentialSwitchTt
| SequentialSwitch of type0 * 'var_t

(** val uCompleteSwitch :
    'a2 switch_style -> int -> 'a2 -> (index -> ('a1, 'a2, 'a3, 'a4, 'a5)
    uaction) -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction **)

let uCompleteSwitch style sz0 var branch_bodies =
  let branches = fun bodies -> gen_branches sz0 (pow2 sz0) bodies in
  (match style with
   | TreeSwitch ->
     uCompleteMuxTree sz0 var (fun bs ->
       branch_bodies (Bits.to_index_safe sz0 bs))
   | OrTreeSwitch nbits ->
     uCompleteOrTree sz0 nbits var (fun bs ->
       branch_bodies (Bits.to_index_safe sz0 bs))
   | NestedSwitch ->
     uswitch_nodefault (UVar var)
       (pred (Nat.pow (Pervasives.succ (Pervasives.succ 0)) sz0))
       (Obj.magic branches branch_bodies)
   | SequentialSwitchTt ->
     uswitch_stateful (UVar var) (pow2 sz0) (branches branch_bodies)
   | SequentialSwitch (output_type, output_var) ->
     let branch_bodies0 = fun idx -> UAssign (output_var, (branch_bodies idx))
     in
     UBind (output_var, (uinit output_type), (USeq
     ((uswitch_stateful (UVar var) (pow2 sz0) (branches branch_bodies0)),
     (UVar output_var)))))

(** val infix_action :
    ('a3 -> int) -> ('a4 -> cExternalSignature) -> lsig -> lsig -> lsig ->
    int -> ('a1, 'a2, 'a3, 'a4) action0 -> ('a1, 'a2, 'a3, 'a4) action0 **)

let rec infix_action cR cSigma infix sig1 sig' _ = function
| Fail0 (_, sz0) -> Fail0 ((app sig1 (app infix sig')), sz0)
| Var0 (_, k, sz0, m) ->
  Var0 ((app sig1 (app infix sig')), k, sz0, (minfix infix sig1 sig' sz0 m))
| Const0 (_, sz0, cst) -> Const0 ((app sig1 (app infix sig')), sz0, cst)
| Assign0 (_, k, sz0, m, a0) ->
  Assign0 ((app sig1 (app infix sig')), k, sz0,
    (minfix infix sig1 sig' sz0 m),
    (infix_action cR cSigma infix sig1 sig' sz0 a0))
| Seq0 (_, sz0, a1, a2) ->
  Seq0 ((app sig1 (app infix sig')), sz0,
    (infix_action cR cSigma infix sig1 sig' 0 a1),
    (infix_action cR cSigma infix sig1 sig' sz0 a2))
| Bind0 (_, k, sz0, sz', a1, a2) ->
  Bind0 ((app sig1 (app infix sig')), k, sz0, sz',
    (infix_action cR cSigma infix sig1 sig' sz0 a1),
    (infix_action cR cSigma infix (sz0 :: sig1) sig' sz' a2))
| If0 (_, sz0, a1, a2, a3) ->
  If0 ((app sig1 (app infix sig')), sz0,
    (infix_action cR cSigma infix sig1 sig' (Pervasives.succ 0) a1),
    (infix_action cR cSigma infix sig1 sig' sz0 a2),
    (infix_action cR cSigma infix sig1 sig' sz0 a3))
| Read0 (_, port0, idx) -> Read0 ((app sig1 (app infix sig')), port0, idx)
| Write0 (_, port0, idx, a0) ->
  Write0 ((app sig1 (app infix sig')), port0, idx,
    (infix_action cR cSigma infix sig1 sig' (cR idx) a0))
| Unop0 (_, fn, a0) ->
  Unop0 ((app sig1 (app infix sig')), fn,
    (infix_action cR cSigma infix sig1 sig'
      (vect_hd 0 (Obj.magic (CircuitSignatures.coq_CSigma1 fn).argSigs)) a0))
| Binop0 (_, fn, a1, a2) ->
  Binop0 ((app sig1 (app infix sig')), fn,
    (infix_action cR cSigma infix sig1 sig'
      (vect_hd (Pervasives.succ 0)
        (Obj.magic (CircuitSignatures.coq_CSigma2 fn).argSigs)) a1),
    (infix_action cR cSigma infix sig1 sig'
      (vect_hd 0
        (Obj.magic vect_tl (Pervasives.succ 0)
          (CircuitSignatures.coq_CSigma2 fn).argSigs)) a2))
| ExternalCall0 (_, fn, a0) ->
  ExternalCall0 ((app sig1 (app infix sig')), fn,
    (infix_action cR cSigma infix sig1 sig'
      (vect_hd 0 (Obj.magic (cSigma fn).argSigs)) a0))
| APos0 (_, sz0, _, a0) -> infix_action cR cSigma infix sig1 sig' sz0 a0

(** val prefix_action :
    ('a3 -> int) -> ('a4 -> cExternalSignature) -> lsig -> lsig -> int ->
    ('a1, 'a2, 'a3, 'a4) action0 -> ('a1, 'a2, 'a3, 'a4) action0 **)

let prefix_action cR cSigma prefix sig1 sz0 a =
  infix_action cR cSigma prefix [] sig1 sz0 a

(** val suffix_action :
    ('a3 -> int) -> ('a4 -> cExternalSignature) -> lsig -> lsig -> int ->
    ('a1, 'a2, 'a3, 'a4) action0 -> ('a1, 'a2, 'a3, 'a4) action0 **)

let suffix_action cR cSigma suffix sig1 sz0 a =
  infix_action cR cSigma suffix sig1 [] sz0 a

(** val lsig_of_tsig : 'a1 tsig -> lsig **)

let lsig_of_tsig sig1 =
  map (fun k_tau -> type_sz (snd k_tau)) sig1

(** val internalCall' :
    ('a3 -> int) -> ('a4 -> cExternalSignature) -> int -> lsig -> lsig ->
    (int, 'a2 * ('a1, 'a2, 'a3, 'a4) action0) context -> ('a1, 'a2, 'a3, 'a4)
    action0 -> ('a1, 'a2, 'a3, 'a4) action0 **)

let rec internalCall' cR cSigma sz0 sig1 _ args fn_body =
  match args with
  | CtxEmpty -> fn_body
  | CtxCons (sig2, sz1, v0, tl) ->
    let (k, v) = v0 in
    let fn_body0 = Bind0 ((app sig2 sig1), k, sz1, sz0,
      (prefix_action cR cSigma sig2 sig1 sz1 v), fn_body)
    in
    internalCall' cR cSigma sz0 sig1 sig2 tl fn_body0

(** val internalCall :
    ('a3 -> int) -> ('a4 -> cExternalSignature) -> int -> lsig -> lsig ->
    (int, 'a2 * ('a1, 'a2, 'a3, 'a4) action0) context -> ('a1, 'a2, 'a3, 'a4)
    action0 -> ('a1, 'a2, 'a3, 'a4) action0 **)

let internalCall cR cSigma sz0 sig1 fn_sig args fn_body =
  internalCall' cR cSigma sz0 sig1 fn_sig args
    (suffix_action cR cSigma sig1 fn_sig sz0 fn_body)

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
     | UConstBits (sz0, bs) -> UConst ((Bits_t sz0), bs)
     | UConstString s0 ->
       UConst ((Array_t { array_type = (Bits_t (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))));
         array_len = (length0 s0) }), (array_of_bytes s0))
     | UConstEnum (sig1, name) ->
       (match vect_index sig1.enum_size eqDec_string name sig1.enum_members with
        | Some idx ->
          UConst ((Enum_t sig1),
            (vect_nth sig1.enum_size sig1.enum_bitpatterns idx))
        | None ->
          UError { epos = pos; emsg = (UnboundEnumMember (name, sig1)) })
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
     | UStructInit (sig1, fields) ->
       let fields0 = map (fun pat -> let (f, a) = pat in (f, (d a))) fields in
       ustruct_init sig1 fields0
     | UArrayInit (tau, elements) ->
       let sig1 = { array_type = tau; array_len = (length elements) } in
       let usubst = fun pos0 x x0 -> UBinop ((PrimUntyped.UArray2
         (PrimUntyped.USubstElement pos0)), x, x0)
       in
       let empty = uinit (Array_t sig1) in
       snd
         (fold_left (fun pat a ->
           let (pos0, acc) = pat in
           ((Pervasives.succ pos0), (usubst pos0 acc (d a)))) elements (0,
           empty))
     | UCallModule (_, fR', fSigma', fn, args) ->
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

let lift_fn1_tc_result r0 sigma sig1 tau pos e r1 =
  result_map_failure (fun pat ->
    let (_, err) = pat in lift_basic_error_message r0 sigma pos sig1 tau e err)
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

let cast_action r0 sigma pos sig1 tau1 tau2 e =
  cast_action' r0 sigma pos sig1 tau1 tau2 e (BasicError (TypeMismatch (tau1,
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

let rec assert_argtypes' r0 sigma sig1 src nexpected fn_name pos args_desc args =
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
       (match cast_action r0 sigma pos1 sig1 (projT1 arg1) tau1 (projT2 arg1) with
        | Success arg2 ->
          (match assert_argtypes' r0 sigma sig1 src nexpected fn_name pos
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

let assert_argtypes r0 sigma sig1 src fn_name pos args_desc args =
  assert_argtypes' r0 sigma sig1 src (length args_desc) fn_name pos args_desc
    args

(** val type_action :
    'a3 eqDec -> ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a1 -> 'a3
    tsig -> ('a1, 'a3, 'a2, 'a4, 'a5) uaction -> ((type0, ('a1, 'a3, 'a2,
    'a4, 'a5) action) sigT, ('a1, 'a3, 'a2) error) result **)

let rec type_action var_t_eq_dec r0 sigma pos sig1 e = match e with
| UError err -> Failure err
| UFail tau -> Success (ExistT (tau, (Fail (sig1, tau))))
| UVar var ->
  (match opt_result (assoc var_t_eq_dec var sig1)
           (mkerror pos (UnboundVariable var) e) with
   | Success tau_m ->
     Success (ExistT ((projT1 tau_m), (Var (sig1, var, (projT1 tau_m),
       (projT2 tau_m)))))
   | Failure f -> Failure f)
| UConst (tau, cst) -> Success (ExistT (tau, (Const (sig1, tau, cst))))
| UAssign (var, ex) ->
  (match opt_result (assoc var_t_eq_dec var sig1)
           (mkerror pos (UnboundVariable var) e) with
   | Success tau_m ->
     (match type_action var_t_eq_dec r0 sigma pos sig1 ex with
      | Success ex' ->
        (match cast_action r0 sigma (actpos pos ex) sig1 (projT1 ex')
                 (projT1 tau_m) (projT2 ex') with
         | Success ex'0 ->
           Success (ExistT ((Bits_t 0), (Assign (sig1, var, (projT1 tau_m),
             (projT2 tau_m), ex'0))))
         | Failure f -> Failure f)
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| USeq (r1, r2) ->
  (match type_action var_t_eq_dec r0 sigma pos sig1 r1 with
   | Success r1' ->
     (match cast_action r0 sigma (actpos pos r1) sig1 (projT1 r1') (Bits_t 0)
              (projT2 r1') with
      | Success r1'0 ->
        (match type_action var_t_eq_dec r0 sigma pos sig1 r2 with
         | Success r2' ->
           Success (ExistT ((projT1 r2'), (Seq (sig1, (projT1 r2'), r1'0,
             (projT2 r2')))))
         | Failure f -> Failure f)
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UBind (v, ex, body) ->
  (match type_action var_t_eq_dec r0 sigma pos sig1 ex with
   | Success ex0 ->
     (match type_action var_t_eq_dec r0 sigma pos ((v, (projT1 ex0)) :: sig1)
              body with
      | Success body0 ->
        Success (ExistT ((projT1 body0), (Bind (sig1, (projT1 ex0),
          (projT1 body0), v, (projT2 ex0), (projT2 body0)))))
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UIf (cond, tbranch, fbranch) ->
  (match type_action var_t_eq_dec r0 sigma pos sig1 cond with
   | Success cond' ->
     (match cast_action r0 sigma (actpos pos cond) sig1 (projT1 cond')
              (Bits_t (Pervasives.succ 0)) (projT2 cond') with
      | Success cond'0 ->
        (match type_action var_t_eq_dec r0 sigma pos sig1 tbranch with
         | Success tbranch' ->
           (match type_action var_t_eq_dec r0 sigma pos sig1 fbranch with
            | Success fbranch' ->
              (match cast_action r0 sigma (actpos pos fbranch) sig1
                       (projT1 fbranch') (projT1 tbranch') (projT2 fbranch') with
               | Success fbranch'0 ->
                 Success (ExistT ((projT1 tbranch'), (If (sig1,
                   (projT1 tbranch'), cond'0, (projT2 tbranch'), fbranch'0))))
               | Failure f -> Failure f)
            | Failure f -> Failure f)
         | Failure f -> Failure f)
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| URead (port0, idx) -> Success (ExistT ((r0 idx), (Read (sig1, port0, idx))))
| UWrite (port0, idx, value) ->
  (match type_action var_t_eq_dec r0 sigma pos sig1 value with
   | Success value' ->
     (match cast_action r0 sigma (actpos pos value) sig1 (projT1 value')
              (r0 idx) (projT2 value') with
      | Success value'0 ->
        Success (ExistT ((Bits_t 0), (Write (sig1, port0, idx, value'0))))
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UUnop (fn, arg1) ->
  let pos1 = actpos pos arg1 in
  (match type_action var_t_eq_dec r0 sigma pos sig1 arg1 with
   | Success arg1' ->
     (match lift_fn1_tc_result r0 sigma sig1 (projT1 arg1') pos1
              (projT2 arg1') (PrimTypeInference.tc1 fn (projT1 arg1')) with
      | Success fn0 ->
        (match cast_action r0 sigma pos1 sig1 (projT1 arg1')
                 (vect_hd 0
                   (Obj.magic (PrimSignatures.coq_Sigma1 fn0).argSigs))
                 (projT2 arg1') with
         | Success arg1'0 ->
           Success (ExistT ((PrimSignatures.coq_Sigma1 fn0).retSig, (Unop
             (sig1, fn0, arg1'0))))
         | Failure f -> Failure f)
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UBinop (fn, arg1, arg2) ->
  let pos1 = actpos pos arg1 in
  let pos2 = actpos pos arg2 in
  (match type_action var_t_eq_dec r0 sigma pos sig1 arg1 with
   | Success arg1' ->
     (match type_action var_t_eq_dec r0 sigma pos sig1 arg2 with
      | Success arg2' ->
        (match lift_fn2_tc_result r0 sigma sig1 (projT1 arg1') sig1
                 (projT1 arg2') pos1 (projT2 arg1') pos2 (projT2 arg2')
                 (PrimTypeInference.tc2 fn (projT1 arg1') (projT1 arg2')) with
         | Success fn0 ->
           (match cast_action r0 sigma pos1 sig1 (projT1 arg1')
                    (vect_hd (Pervasives.succ 0)
                      (Obj.magic (PrimSignatures.coq_Sigma2 fn0).argSigs))
                    (projT2 arg1') with
            | Success arg1'0 ->
              (match cast_action r0 sigma pos2 sig1 (projT1 arg2')
                       (vect_hd 0
                         (Obj.magic vect_tl (Pervasives.succ 0)
                           (PrimSignatures.coq_Sigma2 fn0).argSigs))
                       (projT2 arg2') with
               | Success arg2'0 ->
                 Success (ExistT ((PrimSignatures.coq_Sigma2 fn0).retSig,
                   (Binop (sig1, fn0, arg1'0, arg2'0))))
               | Failure f -> Failure f)
            | Failure f -> Failure f)
         | Failure f -> Failure f)
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UExternalCall (fn, arg1) ->
  let pos1 = actpos pos arg1 in
  (match type_action var_t_eq_dec r0 sigma pos1 sig1 arg1 with
   | Success arg1' ->
     (match cast_action r0 sigma pos1 sig1 (projT1 arg1')
              (vect_hd 0 (Obj.magic (sigma fn).argSigs)) (projT2 arg1') with
      | Success arg1'0 ->
        Success (ExistT ((sigma fn).retSig, (ExternalCall (sig1, fn,
          arg1'0))))
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UInternalCall (fn, args) ->
  (match result_list_map (type_action var_t_eq_dec r0 sigma pos sig1) args with
   | Success tc_args ->
     let arg_positions = map (actpos pos) args in
     let tc_args_w_pos = combine arg_positions tc_args in
     (match assert_argtypes r0 sigma sig1 e fn.int_name pos
              (rev fn.int_argspec) (rev tc_args_w_pos) with
      | Success args_ctx ->
        (match type_action var_t_eq_dec r0 sigma (actpos pos fn.int_body)
                 (rev fn.int_argspec) fn.int_body with
         | Success fn_body' ->
           (match cast_action r0 sigma (actpos pos fn.int_body)
                    (rev fn.int_argspec) (projT1 fn_body') fn.int_retSig
                    (projT2 fn_body') with
            | Success fn_body'0 ->
              Success (ExistT (fn.int_retSig, (InternalCall (sig1,
                fn.int_retSig, fn.int_name, fn.int_argspec, args_ctx,
                fn_body'0))))
            | Failure f -> Failure f)
         | Failure f -> Failure f)
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UAPos (pos0, e0) ->
  (match type_action var_t_eq_dec r0 sigma pos0 sig1 e0 with
   | Success e1 ->
     Success (ExistT ((projT1 e1), (APos (sig1, (projT1 e1), pos0,
       (projT2 e1)))))
   | Failure f -> Failure f)
| USugar _ -> Failure (mkerror pos SugaredConstructorInAst e)

(** val tc_action :
    'a3 eqDec -> ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a1 -> 'a3
    tsig -> type0 -> ('a1, 'a3, 'a2, 'a4, 'a5) uaction -> (('a1, 'a3, 'a2,
    'a4, 'a5) action, ('a1, 'a3, 'a2) error) result **)

let tc_action var_t_eq_dec r0 sigma pos sig1 expected_tau e =
  match type_action var_t_eq_dec r0 sigma pos sig1 e with
  | Success a ->
    cast_action r0 sigma pos sig1 (projT1 a) expected_tau (projT2 a)
  | Failure f -> Failure f

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

(** val unannot :
    int -> ('a1, 'a2, 'a3, 'a4) circuit -> ('a1, 'a2, 'a3, 'a4) circuit **)

let rec unannot _ = function
| CAnnot (sz0, _, c0) -> unannot sz0 c0
| x -> x

(** val asconst :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> int -> ('a1, 'a2, 'a3,
    'a4) circuit -> bool vect option **)

let asconst _ _ sz0 c =
  match unannot sz0 c with
  | CConst (_, cst) -> Some cst
  | _ -> None

(** val isconst :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> int -> ('a1, 'a2, 'a3,
    'a4) circuit -> bool vect -> bool **)

let isconst cR cSigma sz0 c cst =
  match asconst cR cSigma sz0 c with
  | Some cst' -> beq_dec (eqDec_vect sz0 eqDec_bool) cst cst'
  | None -> false

(** val opt_constprop' :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> int -> ('a1, 'a2, 'a3,
    'a4) circuit -> ('a1, 'a2, 'a3, 'a4) circuit **)

let opt_constprop' cR cSigma sz0 c =
  match unannot sz0 c with
  | CMux (_, select, c1, c2) ->
    if isconst cR cSigma (Pervasives.succ 0) select
         (vect_const (Pervasives.succ 0) true)
    then c1
    else if isconst cR cSigma (Pervasives.succ 0) select
              (vect_const (Pervasives.succ 0) false)
         then c2
         else c
  | CUnop (fn, c0) ->
    (match fn with
     | PrimTyped.Not sz1 ->
       (match asconst cR cSigma
                (vect_hd 0
                  (Obj.magic
                    (CircuitSignatures.coq_CSigma1 (PrimTyped.Not sz1)).argSigs))
                c0 with
        | Some cst ->
          CConst
            ((vect_hd 0
               (Obj.magic
                 (CircuitSignatures.coq_CSigma1 (PrimTyped.Not sz1)).argSigs)),
            (Bits.neg
              (vect_hd 0
                (Obj.magic
                  (CircuitSignatures.coq_CSigma1 (PrimTyped.Not sz1)).argSigs))
              cst))
        | None -> c)
     | _ -> c)
  | CBinop (fn, c1, c2) ->
    (match fn with
     | PrimTyped.And sz1 ->
       if (||)
            (isconst cR cSigma
              (vect_hd (Pervasives.succ 0)
                (Obj.magic
                  (CircuitSignatures.coq_CSigma2 (PrimTyped.And sz1)).argSigs))
              c1
              (vect_const
                (vect_hd (Pervasives.succ 0)
                  (Obj.magic
                    (CircuitSignatures.coq_CSigma2 (PrimTyped.And sz1)).argSigs))
                false))
            (isconst cR cSigma
              (vect_hd 0
                (Obj.magic vect_tl (Pervasives.succ 0)
                  (CircuitSignatures.coq_CSigma2 (PrimTyped.And sz1)).argSigs))
              c2
              (vect_const
                (vect_hd 0
                  (Obj.magic vect_tl (Pervasives.succ 0)
                    (CircuitSignatures.coq_CSigma2 (PrimTyped.And sz1)).argSigs))
                false))
       then CConst
              ((CircuitSignatures.coq_CSigma2 (PrimTyped.And sz1)).retSig,
              (vect_const
                (CircuitSignatures.coq_CSigma2 (PrimTyped.And sz1)).retSig
                false))
       else if isconst cR cSigma
                 (vect_hd (Pervasives.succ 0)
                   (Obj.magic
                     (CircuitSignatures.coq_CSigma2 (PrimTyped.And sz1)).argSigs))
                 c1
                 (vect_const
                   (vect_hd (Pervasives.succ 0)
                     (Obj.magic
                       (CircuitSignatures.coq_CSigma2 (PrimTyped.And sz1)).argSigs))
                   true)
            then c2
            else if isconst cR cSigma
                      (vect_hd 0
                        (Obj.magic vect_tl (Pervasives.succ 0)
                          (CircuitSignatures.coq_CSigma2 (PrimTyped.And sz1)).argSigs))
                      c2
                      (vect_const
                        (vect_hd 0
                          (Obj.magic vect_tl (Pervasives.succ 0)
                            (CircuitSignatures.coq_CSigma2 (PrimTyped.And
                              sz1)).argSigs)) true)
                 then c1
                 else c
     | PrimTyped.Or sz1 ->
       if (||)
            (isconst cR cSigma
              (vect_hd (Pervasives.succ 0)
                (Obj.magic
                  (CircuitSignatures.coq_CSigma2 (PrimTyped.Or sz1)).argSigs))
              c1
              (vect_const
                (vect_hd (Pervasives.succ 0)
                  (Obj.magic
                    (CircuitSignatures.coq_CSigma2 (PrimTyped.Or sz1)).argSigs))
                true))
            (isconst cR cSigma
              (vect_hd 0
                (Obj.magic vect_tl (Pervasives.succ 0)
                  (CircuitSignatures.coq_CSigma2 (PrimTyped.Or sz1)).argSigs))
              c2
              (vect_const
                (vect_hd 0
                  (Obj.magic vect_tl (Pervasives.succ 0)
                    (CircuitSignatures.coq_CSigma2 (PrimTyped.Or sz1)).argSigs))
                true))
       then CConst
              ((CircuitSignatures.coq_CSigma2 (PrimTyped.Or sz1)).retSig,
              (vect_const
                (CircuitSignatures.coq_CSigma2 (PrimTyped.Or sz1)).retSig
                true))
       else if isconst cR cSigma
                 (vect_hd (Pervasives.succ 0)
                   (Obj.magic
                     (CircuitSignatures.coq_CSigma2 (PrimTyped.Or sz1)).argSigs))
                 c1
                 (vect_const
                   (vect_hd (Pervasives.succ 0)
                     (Obj.magic
                       (CircuitSignatures.coq_CSigma2 (PrimTyped.Or sz1)).argSigs))
                   false)
            then c2
            else if isconst cR cSigma
                      (vect_hd 0
                        (Obj.magic vect_tl (Pervasives.succ 0)
                          (CircuitSignatures.coq_CSigma2 (PrimTyped.Or sz1)).argSigs))
                      c2
                      (vect_const
                        (vect_hd 0
                          (Obj.magic vect_tl (Pervasives.succ 0)
                            (CircuitSignatures.coq_CSigma2 (PrimTyped.Or sz1)).argSigs))
                        false)
                 then c1
                 else c
     | _ -> c)
  | _ -> c

(** val opt_mux_bit1 :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> int -> ('a1, 'a2, 'a3,
    'a4) circuit -> ('a1, 'a2, 'a3, 'a4) circuit **)

let opt_mux_bit1 cR cSigma sz0 c =
  match unannot sz0 c with
  | CMux (n0, s, c1, c2) ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> c)
       (fun n1 ->
       (fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ ->
         let annot = fun _ c0 -> c0 in
         (match asconst cR cSigma (Pervasives.succ 0) c1 with
          | Some v ->
            let vhd0 = (Obj.magic v).vhd in
            if vhd0
            then (match asconst cR cSigma (Pervasives.succ 0) c2 with
                  | Some v0 ->
                    let vhd1 = (Obj.magic v0).vhd in
                    if vhd1
                    then annot
                           (CircuitSignatures.coq_CSigma2 (PrimTyped.Or
                             (Pervasives.succ 0))).retSig (CBinop
                           ((PrimTyped.Or (Pervasives.succ 0)), s, c2))
                    else annot (Pervasives.succ 0) s
                  | None ->
                    annot
                      (CircuitSignatures.coq_CSigma2 (PrimTyped.Or
                        (Pervasives.succ 0))).retSig (CBinop ((PrimTyped.Or
                      (Pervasives.succ 0)), s, c2)))
            else (match asconst cR cSigma (Pervasives.succ 0) c2 with
                  | Some v0 ->
                    let vhd1 = (Obj.magic v0).vhd in
                    if vhd1
                    then annot
                           (CircuitSignatures.coq_CSigma1 (PrimTyped.Not
                             (Pervasives.succ 0))).retSig (CUnop
                           ((PrimTyped.Not (Pervasives.succ 0)), s))
                    else annot
                           (CircuitSignatures.coq_CSigma2 (PrimTyped.And
                             (Pervasives.succ 0))).retSig (CBinop
                           ((PrimTyped.And (Pervasives.succ 0)), s, c1))
                  | None -> c)
          | None ->
            (match asconst cR cSigma (Pervasives.succ 0) c2 with
             | Some v ->
               let vhd0 = (Obj.magic v).vhd in
               if vhd0
               then c
               else annot
                      (CircuitSignatures.coq_CSigma2 (PrimTyped.And
                        (Pervasives.succ 0))).retSig (CBinop ((PrimTyped.And
                      (Pervasives.succ 0)), s, c1))
             | None -> c)))
         (fun _ -> c)
         n1)
       n0)
  | _ -> c

(** val opt_constprop :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> int -> ('a1, 'a2, 'a3,
    'a4) circuit -> ('a1, 'a2, 'a3, 'a4) circuit **)

let opt_constprop cR cSigma sz0 c =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> CConst (0, (Obj.magic __)))
    (fun n0 ->
    opt_mux_bit1 cR cSigma (Pervasives.succ n0)
      (opt_constprop' cR cSigma (Pervasives.succ n0) c))
    sz0

type lRW =
| LRWRead
| LRWWrite

(** val action_footprint' :
    ('a3 * (lRW * port)) list -> ('a1, 'a2, 'a3, 'a4) action0 ->
    ('a3 * (lRW * port)) list **)

let rec action_footprint' acc = function
| Assign0 (_, _, _, _, ex) -> action_footprint' acc ex
| Seq0 (_, _, r1, r2) -> action_footprint' (action_footprint' acc r1) r2
| Bind0 (_, _, _, _, ex, body) ->
  action_footprint' (action_footprint' acc ex) body
| If0 (_, _, cond, tbranch, fbranch) ->
  action_footprint' (action_footprint' (action_footprint' acc cond) tbranch)
    fbranch
| Read0 (_, port0, idx) -> (idx, (LRWRead, port0)) :: acc
| Write0 (_, port0, idx, value) ->
  action_footprint' ((idx, (LRWWrite, port0)) :: acc) value
| Unop0 (_, _, arg1) -> action_footprint' acc arg1
| Binop0 (_, _, arg1, arg2) ->
  action_footprint' (action_footprint' acc arg1) arg2
| ExternalCall0 (_, _, arg) -> action_footprint' acc arg
| APos0 (_, _, _, a0) -> action_footprint' acc a0
| _ -> acc

(** val action_footprint :
    ('a1, 'a2, 'a3, 'a4) action0 -> ('a3 * (lRW * port)) list **)

let action_footprint a =
  action_footprint' [] a

(** val action_registers :
    ('a3 -> int) -> ('a4 -> cExternalSignature) -> lsig -> int -> 'a3 eqDec
    -> ('a1, 'a2, 'a3, 'a4) action0 -> 'a3 list **)

let action_registers _ _ _ _ eQ a =
  dedup eQ [] (map (fun pat -> let (rs, _) = pat in rs) (action_footprint a))

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

(** val readRegisters :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 -> ('a1, 'a2, 'a3,
    ('a1, 'a2, 'a3) rwdata) circuit **)

let readRegisters _ _ idx =
  CReadRegister idx

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

(** val mux_rwdata :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
    ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3)
    rwdata) circuit) -> int -> char list -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3)
    rwdata) circuit -> ('a1, 'a2, 'a3) rwdata -> ('a1, 'a2, 'a3) rwdata ->
    ('a1, 'a2, 'a3) rwdata **)

let mux_rwdata _ _ opt sz0 an cond tReg fReg =
  { read0 = (CAnnot ((Pervasives.succ 0), an,
    (opt (Pervasives.succ 0) (CMux ((Pervasives.succ 0), cond, tReg.read0,
      fReg.read0))))); read1 = (CAnnot ((Pervasives.succ 0), an,
    (opt (Pervasives.succ 0) (CMux ((Pervasives.succ 0), cond, tReg.read1,
      fReg.read1))))); write0 = (CAnnot ((Pervasives.succ 0), an,
    (opt (Pervasives.succ 0) (CMux ((Pervasives.succ 0), cond, tReg.write0,
      fReg.write0))))); write1 = (CAnnot ((Pervasives.succ 0), an,
    (opt (Pervasives.succ 0) (CMux ((Pervasives.succ 0), cond, tReg.write1,
      fReg.write1))))); data0 = (CAnnot (sz0, an,
    (opt sz0 (CMux (sz0, cond, tReg.data0, fReg.data0))))); data1 = (CAnnot
    (sz0, an, (opt sz0 (CMux (sz0, cond, tReg.data1, fReg.data1))))) }

(** val mux_rwsets :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> (int -> ('a1,
    'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2,
    'a3) rwdata) circuit) -> char list -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3)
    rwdata) circuit -> ('a1, 'a2, 'a3) rwset -> ('a1, 'a2, 'a3) rwset ->
    ('a2, ('a1, 'a2, 'a3) rwdata) env_t **)

let mux_rwsets cR cSigma rEnv opt an cond tRegs fRegs =
  map2 rEnv (fun k treg freg ->
    mux_rwdata cR cSigma opt (cR k) an cond treg freg) tRegs fRegs

(** val mux_ccontext :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
    ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3)
    rwdata) circuit) -> lsig -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
    circuit -> ('a1, 'a2, 'a3) ccontext -> ('a1, 'a2, 'a3) ccontext -> ('a1,
    'a2, 'a3) ccontext **)

let rec mux_ccontext cR cSigma opt sig1 cond ctxT ctxF =
  match sig1 with
  | [] -> CtxEmpty
  | sz0 :: sig2 ->
    CtxCons (sig2, sz0, (CAnnot (sz0,
      ('m'::('u'::('x'::('_'::('c'::('c'::('o'::('n'::('t'::('e'::('x'::('t'::[])))))))))))),
      (opt sz0 (CMux (sz0, cond, (chd sz0 sig2 ctxT), (chd sz0 sig2 ctxF)))))),
      (mux_ccontext cR cSigma opt sig2 cond (ctl sz0 sig2 ctxT)
        (ctl sz0 sig2 ctxF)))

(** val compile_unop :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
    ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3)
    rwdata) circuit) -> PrimTyped.fbits1 -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3)
    rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit **)

let compile_unop _ _ opt fn a =
  let c =
    let c = CUnop (fn, a) in
    (match fn with
     | PrimTyped.SExt (sz0, width) ->
       opt
         (CircuitSignatures.coq_CSigma2 (PrimTyped.Concat
           ((CircuitSignatures.coq_CSigma1 (PrimTyped.Repeat
              ((Pervasives.succ 0), (sub width sz0)))).retSig, sz0))).retSig
         (CBinop ((PrimTyped.Concat
         ((CircuitSignatures.coq_CSigma1 (PrimTyped.Repeat ((Pervasives.succ
            0), (sub width sz0)))).retSig, sz0)),
         (opt
           (CircuitSignatures.coq_CSigma1 (PrimTyped.Repeat ((Pervasives.succ
             0), (sub width sz0)))).retSig (CUnop ((PrimTyped.Repeat
           ((Pervasives.succ 0), (sub width sz0))),
           (opt (CircuitSignatures.coq_CSigma2 (PrimTyped.Sel sz0)).retSig
             (CBinop ((PrimTyped.Sel sz0), a, (CConst ((Nat.log2_up sz0),
             (Bits.of_nat (Nat.log2_up sz0) (pred sz0)))))))))), a))
     | PrimTyped.ZExtL (sz0, width) ->
       opt
         (CircuitSignatures.coq_CSigma2 (PrimTyped.Concat ((sub width sz0),
           sz0))).retSig (CBinop ((PrimTyped.Concat ((sub width sz0), sz0)),
         (CConst
         ((vect_hd (Pervasives.succ 0)
            (Obj.magic
              (CircuitSignatures.coq_CSigma2 (PrimTyped.Concat
                ((sub width sz0), sz0))).argSigs)),
         (Bits.zero
           (vect_hd (Pervasives.succ 0)
             (Obj.magic
               (CircuitSignatures.coq_CSigma2 (PrimTyped.Concat
                 ((sub width sz0), sz0))).argSigs))))), a))
     | PrimTyped.ZExtR (sz0, width) ->
       opt
         (CircuitSignatures.coq_CSigma2 (PrimTyped.Concat
           ((vect_hd 0
              (Obj.magic
                (CircuitSignatures.coq_CSigma1 (PrimTyped.ZExtR (sz0, width))).argSigs)),
           (sub width sz0)))).retSig (CBinop ((PrimTyped.Concat
         ((vect_hd 0
            (Obj.magic
              (CircuitSignatures.coq_CSigma1 (PrimTyped.ZExtR (sz0, width))).argSigs)),
         (sub width sz0))), a, (CConst
         ((vect_hd 0
            (Obj.magic vect_tl (Pervasives.succ 0)
              (CircuitSignatures.coq_CSigma2 (PrimTyped.Concat
                ((vect_hd 0
                   (Obj.magic
                     (CircuitSignatures.coq_CSigma1 (PrimTyped.ZExtR (sz0,
                       width))).argSigs)), (sub width sz0)))).argSigs)),
         (Bits.zero
           (vect_hd 0
             (Obj.magic vect_tl (Pervasives.succ 0)
               (CircuitSignatures.coq_CSigma2 (PrimTyped.Concat
                 ((vect_hd 0
                    (Obj.magic
                      (CircuitSignatures.coq_CSigma1 (PrimTyped.ZExtR (sz0,
                        width))).argSigs)), (sub width sz0)))).argSigs)))))))
     | PrimTyped.Lowered _ -> CConst (0, (Obj.magic __))
     | _ -> c)
  in
  opt (CircuitSignatures.coq_CSigma1 fn).retSig c

(** val slice_subst_macro :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
    ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3)
    rwdata) circuit) -> int -> int -> int -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3)
    rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit ->
    ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit **)

let slice_subst_macro _ _ opt sz0 offset width c1 c2 =
  if le_gt_dec offset sz0
  then opt
         (CircuitSignatures.coq_CSigma2 (PrimTyped.Concat
           ((let rec sub0 n0 m =
               (fun fO fS n -> if n=0 then fO () else fS (n-1))
                 (fun _ -> n0)
                 (fun k ->
                 (fun fO fS n -> if n=0 then fO () else fS (n-1))
                   (fun _ -> n0)
                   (fun l -> sub0 k l)
                   m)
                 n0
             in sub0 sz0 offset), offset))).retSig (CBinop ((PrimTyped.Concat
         ((let rec sub0 n0 m =
             (fun fO fS n -> if n=0 then fO () else fS (n-1))
               (fun _ -> n0)
               (fun k ->
               (fun fO fS n -> if n=0 then fO () else fS (n-1))
                 (fun _ -> n0)
                 (fun l -> sub0 k l)
                 m)
               n0
           in sub0 sz0 offset), offset)),
         (if le_gt_dec width (sub sz0 offset)
          then opt
                 (CircuitSignatures.coq_CSigma2 (PrimTyped.Concat
                   ((CircuitSignatures.coq_CSigma1 (PrimTyped.Slice (sz0,
                      (add offset width), (sub (sub sz0 offset) width)))).retSig,
                   width))).retSig (CBinop ((PrimTyped.Concat
                 ((CircuitSignatures.coq_CSigma1 (PrimTyped.Slice (sz0,
                    (add offset width), (sub (sub sz0 offset) width)))).retSig,
                 width)),
                 (opt
                   (CircuitSignatures.coq_CSigma1 (PrimTyped.Slice (sz0,
                     (add offset width), (sub (sub sz0 offset) width)))).retSig
                   (CUnop ((PrimTyped.Slice (sz0, (add offset width),
                   (sub (sub sz0 offset) width))), c1))), c2))
          else opt
                 (CircuitSignatures.coq_CSigma1 (PrimTyped.Slice (width, 0,
                   (sub sz0 offset)))).retSig (CUnop ((PrimTyped.Slice
                 (width, 0, (sub sz0 offset))), c2))),
         (opt
           (CircuitSignatures.coq_CSigma1 (PrimTyped.Slice (sz0, 0, offset))).retSig
           (CUnop ((PrimTyped.Slice (sz0, 0, offset)), c1)))))
  else c1

(** val compile_binop :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
    ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3)
    rwdata) circuit) -> PrimTyped.fbits2 -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3)
    rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit ->
    ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit **)

let compile_binop cR cSigma opt fn c1 c2 =
  let c =
    let c = CBinop (fn, c1, c2) in
    (match fn with
     | PrimTyped.SliceSubst (sz0, offset, width) ->
       slice_subst_macro cR cSigma opt
         (vect_hd (Pervasives.succ 0)
           (Obj.magic
             (CircuitSignatures.coq_CSigma2 (PrimTyped.SliceSubst (sz0,
               offset, width))).argSigs)) offset
         (vect_hd 0
           (Obj.magic vect_tl (Pervasives.succ 0)
             (CircuitSignatures.coq_CSigma2 (PrimTyped.SliceSubst (sz0,
               offset, width))).argSigs)) c1 c2
     | _ -> c)
  in
  opt (CircuitSignatures.coq_CSigma2 fn).retSig c

(** val compile_action :
    ('a4 -> int) -> ('a5 -> cExternalSignature) -> 'a4 env -> 'a2 show ->
    (int -> ('a3, 'a4, 'a5, ('a3, 'a4, 'a5) rwdata) circuit -> ('a3, 'a4,
    'a5, ('a3, 'a4, 'a5) rwdata) circuit) -> ('a4, ('a3, 'a4, 'a5, ('a3, 'a4,
    'a5) rwdata) circuit) env_t -> lsig -> int -> ('a3, 'a4, 'a5) ccontext ->
    ('a1, 'a2, 'a4, 'a5) action0 -> ('a3, 'a4, 'a5) rwcircuit -> ('a3, 'a4,
    'a5) action_circuit * ('a3, 'a4, 'a5) ccontext **)

let rec compile_action cR cSigma rEnv show_var_t opt cr _ _ gamma a clog =
  match a with
  | Fail0 (_, sz0) ->
    ({ erwc = { canFire = (CAnnot ((Pervasives.succ 0),
      ('f'::('a'::('i'::('l'::('_'::('c'::('a'::('n'::('F'::('i'::('r'::('e'::[])))))))))))),
      (opt (Pervasives.succ 0) (CConst ((Pervasives.succ 0),
        (Obj.magic vect_cons 0 false __)))))); regs = clog.regs }; retVal =
      (CAnnot (sz0, ('f'::('a'::('i'::('l'::[])))),
      (opt sz0 (CConst (sz0, (vect_const sz0 false)))))) }, gamma)
  | Var0 (sig1, k, sz0, m) ->
    ({ erwc = clog; retVal = (CAnnot (sz0,
      (append ('v'::('a'::('r'::('_'::[])))) (show_var_t.show0 k)),
      (opt sz0 (cassoc sig1 sz0 m gamma)))) }, gamma)
  | Const0 (_, sz0, cst) ->
    ({ erwc = clog; retVal = (CConst (sz0, cst)) }, gamma)
  | Assign0 (sig1, _, sz0, m, ex) ->
    let (cex, gamma0) =
      compile_action cR cSigma rEnv show_var_t opt cr sig1 sz0 gamma ex clog
    in
    ({ erwc = cex.erwc; retVal = (CAnnot (0,
    ('a'::('s'::('s'::('i'::('g'::('n'::('_'::('r'::('e'::('t'::('V'::('a'::('l'::[]))))))))))))),
    (opt 0 (CConst (0, (Obj.magic __)))))) },
    (creplace sig1 sz0 m cex.retVal gamma0))
  | Seq0 (sig1, sz0, r1, r2) ->
    let (cex, gamma0) =
      compile_action cR cSigma rEnv show_var_t opt cr sig1 0 gamma r1 clog
    in
    compile_action cR cSigma rEnv show_var_t opt cr sig1 sz0 gamma0 r2
      cex.erwc
  | Bind0 (sig1, _, sz0, sz', ex, body) ->
    let (ex0, gamma0) =
      compile_action cR cSigma rEnv show_var_t opt cr sig1 sz0 gamma ex clog
    in
    let (ex1, gamma1) =
      compile_action cR cSigma rEnv show_var_t opt cr (sz0 :: sig1) sz'
        (CtxCons (sig1, sz0, ex0.retVal, gamma0)) body ex0.erwc
    in
    (ex1, (ctl sz0 sig1 gamma1))
  | If0 (sig1, sz0, cond, tbranch, fbranch) ->
    let (cond0, gamma0) =
      compile_action cR cSigma rEnv show_var_t opt cr sig1 (Pervasives.succ
        0) gamma cond clog
    in
    let (tbranch0, gamma_t) =
      compile_action cR cSigma rEnv show_var_t opt cr sig1 sz0 gamma0 tbranch
        cond0.erwc
    in
    let (fbranch0, gamma_f) =
      compile_action cR cSigma rEnv show_var_t opt cr sig1 sz0 gamma0 fbranch
        cond0.erwc
    in
    let cond_val = CAnnot ((Pervasives.succ 0),
      ('c'::('o'::('n'::('d'::[])))), (opt (Pervasives.succ 0) cond0.retVal))
    in
    ({ erwc = { canFire = (CAnnot ((Pervasives.succ 0),
    ('i'::('f'::('_'::('c'::('a'::('n'::('F'::('i'::('r'::('e'::[])))))))))),
    (opt (Pervasives.succ 0) (CMux ((Pervasives.succ 0), cond_val,
      tbranch0.erwc.canFire, fbranch0.erwc.canFire))))); regs =
    (mux_rwsets cR cSigma rEnv opt
      ('i'::('f'::('_'::('m'::('u'::('x'::[])))))) cond_val
      tbranch0.erwc.regs fbranch0.erwc.regs) }; retVal = (CAnnot (sz0,
    ('i'::('f'::('_'::('r'::('e'::('t'::('V'::('a'::('l'::[]))))))))),
    (opt sz0 (CMux (sz0, cond_val, tbranch0.retVal, fbranch0.retVal))))) },
    (mux_ccontext cR cSigma opt sig1 cond_val gamma_t gamma_f))
  | Read0 (_, port0, idx) ->
    (match port0 with
     | P0 ->
       let reg = getenv rEnv clog.regs idx in
       ({ erwc = { canFire = clog.canFire; regs =
       (putenv rEnv clog.regs idx { read0 = (CAnnot ((Pervasives.succ 0),
         ('r'::('e'::('a'::('d'::('0'::[]))))),
         (opt (Pervasives.succ 0) (CConst ((Pervasives.succ 0),
           (Obj.magic vect_cons 0 true __)))))); read1 = reg.read1; write0 =
         reg.write0; write1 = reg.write1; data0 = reg.data0; data1 =
         reg.data1 }) }; retVal = (getenv rEnv cr idx) }, gamma)
     | P1 ->
       let reg = getenv rEnv clog.regs idx in
       ({ erwc = { canFire = clog.canFire; regs =
       (putenv rEnv clog.regs idx { read0 = reg.read0; read1 = (CAnnot
         ((Pervasives.succ 0), ('r'::('e'::('a'::('d'::('1'::[]))))),
         (opt (Pervasives.succ 0) (CConst ((Pervasives.succ 0),
           (Obj.magic vect_cons 0 true __)))))); write0 = reg.write0;
         write1 = reg.write1; data0 = reg.data0; data1 = reg.data1 }) };
       retVal = reg.data0 }, gamma))
  | Write0 (sig1, port0, idx, val0) ->
    (match port0 with
     | P0 ->
       let (val1, gamma0) =
         compile_action cR cSigma rEnv show_var_t opt cr sig1 (cR idx) gamma
           val0 clog
       in
       let reg = getenv rEnv val1.erwc.regs idx in
       ({ erwc = { canFire = (CAnnot
       ((CircuitSignatures.coq_CSigma2 (PrimTyped.And (Pervasives.succ 0))).retSig,
       ('w'::('r'::('i'::('t'::('e'::('0'::('_'::('c'::('a'::('n'::('F'::('i'::('r'::('e'::[])))))))))))))),
       (opt
         (CircuitSignatures.coq_CSigma2 (PrimTyped.And (Pervasives.succ 0))).retSig
         (CBinop ((PrimTyped.And (Pervasives.succ 0)), val1.erwc.canFire,
         (CAnnot
         ((CircuitSignatures.coq_CSigma2 (PrimTyped.And
            (CircuitSignatures.coq_CSigma2 (PrimTyped.And
              (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ
                0))).retSig)).retSig)).retSig,
         ('w'::('r'::('i'::('t'::('e'::('0'::('_'::('c'::('a'::('n'::('F'::('i'::('r'::('e'::[])))))))))))))),
         (opt
           (CircuitSignatures.coq_CSigma2 (PrimTyped.And
             (CircuitSignatures.coq_CSigma2 (PrimTyped.And
               (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ
                 0))).retSig)).retSig)).retSig (CBinop ((PrimTyped.And
           (CircuitSignatures.coq_CSigma2 (PrimTyped.And
             (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ
               0))).retSig)).retSig), (CAnnot
           ((CircuitSignatures.coq_CSigma2 (PrimTyped.And
              (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ
                0))).retSig)).retSig,
           ('w'::('r'::('i'::('t'::('e'::('0'::('_'::('c'::('a'::('n'::('F'::('i'::('r'::('e'::[])))))))))))))),
           (opt
             (CircuitSignatures.coq_CSigma2 (PrimTyped.And
               (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ
                 0))).retSig)).retSig (CBinop ((PrimTyped.And
             (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ
               0))).retSig), (CAnnot
             ((CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ
                0))).retSig,
             ('n'::('o'::('_'::('r'::('e'::('a'::('d'::('1'::[])))))))),
             (opt
               (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ
                 0))).retSig (CUnop ((PrimTyped.Not (Pervasives.succ 0)),
               reg.read1))))), (CAnnot
             ((CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ
                0))).retSig,
             ('n'::('o'::('_'::('w'::('r'::('i'::('t'::('e'::('0'::[]))))))))),
             (opt
               (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ
                 0))).retSig (CUnop ((PrimTyped.Not (Pervasives.succ 0)),
               reg.write0)))))))))), (CAnnot
           ((CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ
              0))).retSig,
           ('n'::('o'::('_'::('w'::('r'::('i'::('t'::('e'::('1'::[]))))))))),
           (opt
             (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ
               0))).retSig (CUnop ((PrimTyped.Not (Pervasives.succ 0)),
             reg.write1))))))))))))))); regs =
       (putenv rEnv val1.erwc.regs idx { read0 = reg.read0; read1 =
         reg.read1; write0 = (CAnnot ((Pervasives.succ 0),
         ('w'::('r'::('i'::('t'::('e'::('0'::[])))))),
         (opt (Pervasives.succ 0) (CConst ((Pervasives.succ 0),
           (Obj.magic vect_cons 0 true __)))))); write1 = reg.write1; data0 =
         val1.retVal; data1 = reg.data1 }) }; retVal = (CAnnot (0,
       ('w'::('r'::('i'::('t'::('e'::('_'::('r'::('e'::('t'::('V'::('a'::('l'::[])))))))))))),
       (opt 0 (CConst (0, (Obj.magic __)))))) }, gamma0)
     | P1 ->
       let (val1, gamma0) =
         compile_action cR cSigma rEnv show_var_t opt cr sig1 (cR idx) gamma
           val0 clog
       in
       let reg = getenv rEnv val1.erwc.regs idx in
       ({ erwc = { canFire = (CAnnot
       ((CircuitSignatures.coq_CSigma2 (PrimTyped.And (Pervasives.succ 0))).retSig,
       ('w'::('r'::('i'::('t'::('e'::('1'::('_'::('c'::('a'::('n'::('F'::('i'::('r'::('e'::[])))))))))))))),
       (opt
         (CircuitSignatures.coq_CSigma2 (PrimTyped.And (Pervasives.succ 0))).retSig
         (CBinop ((PrimTyped.And (Pervasives.succ 0)), val1.erwc.canFire,
         (CAnnot
         ((CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ 0))).retSig,
         ('n'::('o'::('_'::('w'::('r'::('i'::('t'::('e'::('1'::[]))))))))),
         (opt
           (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ 0))).retSig
           (CUnop ((PrimTyped.Not (Pervasives.succ 0)), reg.write1))))))))));
       regs =
       (putenv rEnv val1.erwc.regs idx { read0 = reg.read0; read1 =
         reg.read1; write0 = reg.write0; write1 = (CAnnot ((Pervasives.succ
         0), ('w'::('r'::('i'::('t'::('e'::('1'::[])))))),
         (opt (Pervasives.succ 0) (CConst ((Pervasives.succ 0),
           (Obj.magic vect_cons 0 true __)))))); data0 = reg.data0; data1 =
         val1.retVal }) }; retVal = (CAnnot (0,
       ('w'::('r'::('i'::('t'::('e'::('_'::('r'::('e'::('t'::('V'::('a'::('l'::[])))))))))))),
       (opt 0 (CConst (0, (Obj.magic __)))))) }, gamma0))
  | Unop0 (sig1, fn, a0) ->
    let (a1, gamma0) =
      compile_action cR cSigma rEnv show_var_t opt cr sig1
        (vect_hd 0 (Obj.magic (CircuitSignatures.coq_CSigma1 fn).argSigs))
        gamma a0 clog
    in
    ({ erwc = a1.erwc; retVal = (compile_unop cR cSigma opt fn a1.retVal) },
    gamma0)
  | Binop0 (sig1, fn, a1, a2) ->
    let (a3, gamma0) =
      compile_action cR cSigma rEnv show_var_t opt cr sig1
        (vect_hd (Pervasives.succ 0)
          (Obj.magic (CircuitSignatures.coq_CSigma2 fn).argSigs)) gamma a1
        clog
    in
    let (a4, gamma1) =
      compile_action cR cSigma rEnv show_var_t opt cr sig1
        (vect_hd 0
          (Obj.magic vect_tl (Pervasives.succ 0)
            (CircuitSignatures.coq_CSigma2 fn).argSigs)) gamma0 a2 a3.erwc
    in
    ({ erwc = a4.erwc; retVal =
    (compile_binop cR cSigma opt fn a3.retVal a4.retVal) }, gamma1)
  | ExternalCall0 (sig1, fn, a0) ->
    let (a1, gamma0) =
      compile_action cR cSigma rEnv show_var_t opt cr sig1
        (vect_hd 0 (Obj.magic (cSigma fn).argSigs)) gamma a0 clog
    in
    ({ erwc = a1.erwc; retVal = (CExternal (fn, a1.retVal)) }, gamma0)
  | APos0 (sig1, sz0, _, a0) ->
    compile_action cR cSigma rEnv show_var_t opt cr sig1 sz0 gamma a0 clog

(** val adapter :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> (int -> ('a1,
    'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2,
    'a3) rwdata) circuit) -> ('a1, 'a2, 'a3) scheduler_circuit -> ('a1, 'a2,
    'a3) rwcircuit **)

let adapter _ _ rEnv opt cs =
  { canFire = (CAnnot ((Pervasives.succ 0),
    ('c'::('F'::('_'::('i'::('n'::('i'::('t'::[]))))))),
    (opt (Pervasives.succ 0) (CConst ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 true __)))))); regs =
    (map0 rEnv (fun _ reg -> { read0 = (CAnnot ((Pervasives.succ 0),
      ('i'::('n'::('i'::('t'::('_'::('n'::('o'::('_'::('r'::('e'::('a'::('d'::('0'::[]))))))))))))),
      (opt (Pervasives.succ 0) (CConst ((Pervasives.succ 0),
        (Obj.magic vect_cons 0 false __)))))); read1 = (CAnnot
      ((Pervasives.succ 0),
      ('i'::('n'::('i'::('t'::('_'::('n'::('o'::('_'::('r'::('e'::('a'::('d'::('1'::[]))))))))))))),
      (opt (Pervasives.succ 0) (CConst ((Pervasives.succ 0),
        (Obj.magic vect_cons 0 false __)))))); write0 = (CAnnot
      ((Pervasives.succ 0),
      ('i'::('n'::('i'::('t'::('_'::('n'::('o'::('_'::('w'::('r'::('i'::('t'::('e'::('0'::[])))))))))))))),
      (opt (Pervasives.succ 0) (CConst ((Pervasives.succ 0),
        (Obj.magic vect_cons 0 false __)))))); write1 = (CAnnot
      ((Pervasives.succ 0),
      ('i'::('n'::('i'::('t'::('_'::('n'::('o'::('_'::('w'::('r'::('i'::('t'::('e'::('1'::[])))))))))))))),
      (opt (Pervasives.succ 0) (CConst ((Pervasives.succ 0),
        (Obj.magic vect_cons 0 false __)))))); data0 = reg.data0; data1 =
      reg.data1 }) cs) }

(** val willFire_of_canFire'_read0 :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
    ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3)
    rwdata) circuit) -> int -> ('a1, 'a2, 'a3) rwdata -> ('a1, 'a2, 'a3)
    rwdata -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit **)

let willFire_of_canFire'_read0 _ _ opt _ ruleReg inReg =
  CAnnot
    ((CircuitSignatures.coq_CSigma2 (PrimTyped.Or
       (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ 0))).retSig)).retSig,
    ('r'::('e'::('a'::('d'::('0'::('_'::('w'::('i'::('l'::('l'::('F'::('i'::('r'::('e'::('_'::('o'::('f'::('_'::('c'::('a'::('n'::('F'::('i'::('r'::('e'::[]))))))))))))))))))))))))),
    (opt
      (CircuitSignatures.coq_CSigma2 (PrimTyped.Or
        (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ 0))).retSig)).retSig
      (CBinop ((PrimTyped.Or
      (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ 0))).retSig),
      (CAnnot
      ((CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ 0))).retSig,
      ('i'::('m'::('p'::('l'::[])))),
      (opt
        (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ 0))).retSig
        (CUnop ((PrimTyped.Not (Pervasives.succ 0)), ruleReg.read0))))),
      (CAnnot
      ((CircuitSignatures.coq_CSigma1 (PrimTyped.Not
         (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig)).retSig,
      ('r'::('e'::('a'::('d'::('0'::('_'::('w'::('i'::('l'::('l'::('F'::('i'::('r'::('e'::('_'::('n'::('o'::('_'::('w'::('r'::('i'::('t'::('e'::('s'::[])))))))))))))))))))))))),
      (opt
        (CircuitSignatures.coq_CSigma1 (PrimTyped.Not
          (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig)).retSig
        (CUnop ((PrimTyped.Not
        (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig),
        (CAnnot
        ((CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig,
        [],
        (opt
          (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig
          (CBinop ((PrimTyped.Or (Pervasives.succ 0)), inReg.write0,
          inReg.write1))))))))))))))

(** val willFire_of_canFire'_write0 :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
    ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3)
    rwdata) circuit) -> int -> ('a1, 'a2, 'a3) rwdata -> ('a1, 'a2, 'a3)
    rwdata -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit **)

let willFire_of_canFire'_write0 _ _ opt _ ruleReg inReg =
  CAnnot
    ((CircuitSignatures.coq_CSigma2 (PrimTyped.Or
       (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ 0))).retSig)).retSig,
    ('w'::('r'::('i'::('t'::('e'::('0'::('_'::('w'::('i'::('l'::('l'::('F'::('i'::('r'::('e'::('_'::('o'::('f'::('_'::('c'::('a'::('n'::('F'::('i'::('r'::('e'::[])))))))))))))))))))))))))),
    (opt
      (CircuitSignatures.coq_CSigma2 (PrimTyped.Or
        (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ 0))).retSig)).retSig
      (CBinop ((PrimTyped.Or
      (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ 0))).retSig),
      (CAnnot
      ((CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ 0))).retSig,
      ('i'::('m'::('p'::('l'::[])))),
      (opt
        (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ 0))).retSig
        (CUnop ((PrimTyped.Not (Pervasives.succ 0)), ruleReg.write0))))),
      (CAnnot
      ((CircuitSignatures.coq_CSigma1 (PrimTyped.Not
         (CircuitSignatures.coq_CSigma2 (PrimTyped.Or
           (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig)).retSig)).retSig,
      ('w'::('r'::('i'::('t'::('e'::('0'::('_'::('w'::('i'::('l'::('l'::('F'::('i'::('r'::('e'::('_'::('n'::('o'::('_'::('w'::('r'::('i'::('t'::('e'::('s'::('_'::('n'::('o'::('_'::('r'::('e'::('a'::('d'::('1'::[])))))))))))))))))))))))))))))))))),
      (opt
        (CircuitSignatures.coq_CSigma1 (PrimTyped.Not
          (CircuitSignatures.coq_CSigma2 (PrimTyped.Or
            (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig)).retSig)).retSig
        (CUnop ((PrimTyped.Not
        (CircuitSignatures.coq_CSigma2 (PrimTyped.Or
          (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig)).retSig),
        (CAnnot
        ((CircuitSignatures.coq_CSigma2 (PrimTyped.Or
           (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig)).retSig,
        [],
        (opt
          (CircuitSignatures.coq_CSigma2 (PrimTyped.Or
            (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig)).retSig
          (CBinop ((PrimTyped.Or
          (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig),
          (CAnnot
          ((CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig,
          [],
          (opt
            (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig
            (CBinop ((PrimTyped.Or (Pervasives.succ 0)), inReg.write0,
            inReg.write1))))), inReg.read1))))))))))))))

(** val willFire_of_canFire'_rw1 :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
    ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3)
    rwdata) circuit) -> int -> ('a1, 'a2, 'a3) rwdata -> ('a1, 'a2, 'a3)
    rwdata -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit **)

let willFire_of_canFire'_rw1 _ _ opt _ ruleReg inReg =
  CAnnot
    ((CircuitSignatures.coq_CSigma2 (PrimTyped.Or
       (CircuitSignatures.coq_CSigma1 (PrimTyped.Not
         (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig)).retSig)).retSig,
    ('r'::('e'::('a'::('d'::('_'::('w'::('r'::('i'::('t'::('e'::('1'::('_'::('w'::('i'::('l'::('l'::('F'::('i'::('r'::('e'::('_'::('o'::('f'::('_'::('c'::('a'::('n'::('F'::('i'::('r'::('e'::[]))))))))))))))))))))))))))))))),
    (opt
      (CircuitSignatures.coq_CSigma2 (PrimTyped.Or
        (CircuitSignatures.coq_CSigma1 (PrimTyped.Not
          (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig)).retSig)).retSig
      (CBinop ((PrimTyped.Or
      (CircuitSignatures.coq_CSigma1 (PrimTyped.Not
        (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig)).retSig),
      (CAnnot
      ((CircuitSignatures.coq_CSigma1 (PrimTyped.Not
         (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig)).retSig,
      ('i'::('m'::('p'::('l'::[])))),
      (opt
        (CircuitSignatures.coq_CSigma1 (PrimTyped.Not
          (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig)).retSig
        (CUnop ((PrimTyped.Not
        (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig),
        (CAnnot
        ((CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig,
        [],
        (opt
          (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig
          (CBinop ((PrimTyped.Or (Pervasives.succ 0)), ruleReg.read1,
          ruleReg.write1)))))))))), (CAnnot
      ((CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ 0))).retSig,
      ('r'::('e'::('a'::('d'::('_'::('w'::('r'::('i'::('t'::('e'::('1'::('_'::('w'::('i'::('l'::('l'::('F'::('i'::('r'::('e'::('_'::('n'::('o'::('_'::('w'::('r'::('i'::('t'::('e'::('1'::[])))))))))))))))))))))))))))))),
      (opt
        (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ 0))).retSig
        (CUnop ((PrimTyped.Not (Pervasives.succ 0)), inReg.write1)))))))))

(** val willFire_of_canFire' :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
    ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3)
    rwdata) circuit) -> int -> ('a1, 'a2, 'a3) rwdata -> ('a1, 'a2, 'a3)
    rwdata -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit **)

let willFire_of_canFire' cR cSigma opt sz0 ruleReg inReg =
  CAnnot
    ((CircuitSignatures.coq_CSigma2 (PrimTyped.And
       (CircuitSignatures.coq_CSigma2 (PrimTyped.And
         (CircuitSignatures.coq_CSigma2 (PrimTyped.Or
           (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ 0))).retSig)).retSig)).retSig)).retSig,
    [],
    (opt
      (CircuitSignatures.coq_CSigma2 (PrimTyped.And
        (CircuitSignatures.coq_CSigma2 (PrimTyped.And
          (CircuitSignatures.coq_CSigma2 (PrimTyped.Or
            (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ
              0))).retSig)).retSig)).retSig)).retSig (CBinop ((PrimTyped.And
      (CircuitSignatures.coq_CSigma2 (PrimTyped.And
        (CircuitSignatures.coq_CSigma2 (PrimTyped.Or
          (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ 0))).retSig)).retSig)).retSig),
      (CAnnot
      ((CircuitSignatures.coq_CSigma2 (PrimTyped.And
         (CircuitSignatures.coq_CSigma2 (PrimTyped.Or
           (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ 0))).retSig)).retSig)).retSig,
      [],
      (opt
        (CircuitSignatures.coq_CSigma2 (PrimTyped.And
          (CircuitSignatures.coq_CSigma2 (PrimTyped.Or
            (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ
              0))).retSig)).retSig)).retSig (CBinop ((PrimTyped.And
        (CircuitSignatures.coq_CSigma2 (PrimTyped.Or
          (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ 0))).retSig)).retSig),
        (willFire_of_canFire'_read0 cR cSigma opt sz0 ruleReg inReg),
        (willFire_of_canFire'_write0 cR cSigma opt sz0 ruleReg inReg)))))),
      (willFire_of_canFire'_rw1 cR cSigma opt sz0 ruleReg inReg)))))

(** val willFire_of_canFire :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> 'a1 show ->
    (int -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2,
    'a3, ('a1, 'a2, 'a3) rwdata) circuit) -> 'a1 -> ('a1, 'a2, 'a3) rwcircuit
    -> ('a2, ('a1, 'a2, 'a3) rwdata) env_t -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3)
    rwdata) circuit **)

let willFire_of_canFire cR cSigma rEnv show_rule_name_t opt rl_name cRule cInput =
  let wf = append ('w'::('F'::('_'::[]))) (show_rule_name_t.show0 rl_name) in
  let cf = append ('c'::('F'::('_'::[]))) (show_rule_name_t.show0 rl_name) in
  CAnnot
  ((vect_hd (Pervasives.succ 0)
     (Obj.magic
       (CircuitSignatures.coq_CSigma2 (PrimTyped.And
         (CircuitSignatures.coq_CSigma2 (PrimTyped.And
           (CircuitSignatures.coq_CSigma2 (PrimTyped.And
             (CircuitSignatures.coq_CSigma2 (PrimTyped.Or
               (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ
                 0))).retSig)).retSig)).retSig)).retSig)).argSigs)), wf,
  (fold_right0 rEnv (fun k pat acc ->
    let (ruleReg, inReg) = pat in
    CAnnot
    ((CircuitSignatures.coq_CSigma2 (PrimTyped.And
       (CircuitSignatures.coq_CSigma2 (PrimTyped.And
         (CircuitSignatures.coq_CSigma2 (PrimTyped.And
           (CircuitSignatures.coq_CSigma2 (PrimTyped.Or
             (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ
               0))).retSig)).retSig)).retSig)).retSig)).retSig, wf,
    (opt
      (CircuitSignatures.coq_CSigma2 (PrimTyped.And
        (CircuitSignatures.coq_CSigma2 (PrimTyped.And
          (CircuitSignatures.coq_CSigma2 (PrimTyped.And
            (CircuitSignatures.coq_CSigma2 (PrimTyped.Or
              (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ
                0))).retSig)).retSig)).retSig)).retSig)).retSig (CBinop
      ((PrimTyped.And
      (CircuitSignatures.coq_CSigma2 (PrimTyped.And
        (CircuitSignatures.coq_CSigma2 (PrimTyped.And
          (CircuitSignatures.coq_CSigma2 (PrimTyped.Or
            (CircuitSignatures.coq_CSigma1 (PrimTyped.Not (Pervasives.succ
              0))).retSig)).retSig)).retSig)).retSig), acc,
      (willFire_of_canFire' cR cSigma opt (cR k) ruleReg inReg))))))
    (zip rEnv cRule.regs cInput) (CAnnot ((Pervasives.succ 0), cf,
    cRule.canFire))))

(** val update_accumulated_rwset :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> (int -> ('a1,
    'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2,
    'a3) rwdata) circuit) -> ('a1, 'a2, 'a3) rwset -> ('a1, 'a2, 'a3) rwset
    -> ('a2, ('a1, 'a2, 'a3) rwdata) env_t **)

let update_accumulated_rwset _ _ rEnv opt rl_rwset acc =
  let an =
    'c'::('o'::('m'::('p'::('u'::('t'::('e'::('_'::('a'::('c'::('c'::('u'::('m'::('u'::('l'::('a'::('t'::('e'::('d'::('_'::('r'::('w'::('s'::('e'::('t'::[]))))))))))))))))))))))))
  in
  map2 rEnv (fun _ ruleReg accReg -> { read0 = (CAnnot
    ((CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig,
    an,
    (opt
      (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig
      (CBinop ((PrimTyped.Or (Pervasives.succ 0)), ruleReg.read0,
      accReg.read0))))); read1 = (CAnnot
    ((CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig,
    an,
    (opt
      (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig
      (CBinop ((PrimTyped.Or (Pervasives.succ 0)), ruleReg.read1,
      accReg.read1))))); write0 = (CAnnot
    ((CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig,
    an,
    (opt
      (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig
      (CBinop ((PrimTyped.Or (Pervasives.succ 0)), ruleReg.write0,
      accReg.write0))))); write1 = (CAnnot
    ((CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig,
    an,
    (opt
      (CircuitSignatures.coq_CSigma2 (PrimTyped.Or (Pervasives.succ 0))).retSig
      (CBinop ((PrimTyped.Or (Pervasives.succ 0)), ruleReg.write1,
      accReg.write1))))); data0 = ruleReg.data0; data1 = ruleReg.data1 })
    rl_rwset acc

(** val bundleref_wrap_rwdata :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> 'a1 -> 'a2 list
    -> ('a2, ('a1, 'a2, 'a3) rwdata) context -> 'a2 -> ('a1, 'a2, 'a3) rwdata
    -> ('a1, 'a2, 'a3) rwdata **)

let bundleref_wrap_rwdata cR _ rEnv rl rs bundle r0 ruleReg =
  let ft = rEnv.finite_keys in
  (match find (fun r' -> beq_dec (eqDec_FiniteType ft) r0 r') rs with
   | Some _ ->
     { read0 = (CBundleRef ((Pervasives.succ 0), rl, rs, bundle,
       (Rwcircuit_rwdata (r0, Rwdata_r0)), ruleReg.read0)); read1 =
       (CBundleRef ((Pervasives.succ 0), rl, rs, bundle, (Rwcircuit_rwdata
       (r0, Rwdata_r1)), ruleReg.read1)); write0 = (CBundleRef
       ((Pervasives.succ 0), rl, rs, bundle, (Rwcircuit_rwdata (r0,
       Rwdata_w0)), ruleReg.write0)); write1 = (CBundleRef ((Pervasives.succ
       0), rl, rs, bundle, (Rwcircuit_rwdata (r0, Rwdata_w1)),
       ruleReg.write1)); data0 = (CBundleRef ((cR r0), rl, rs, bundle,
       (Rwcircuit_rwdata (r0, Rwdata_data0)), ruleReg.data0)); data1 =
       (CBundleRef ((cR r0), rl, rs, bundle, (Rwcircuit_rwdata (r0,
       Rwdata_data1)), ruleReg.data1)) }
   | None -> ruleReg)

(** val bundleref_wrap_rwset :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> 'a1 -> 'a2 list
    -> ('a2, ('a1, 'a2, 'a3) rwdata) context -> ('a1, 'a2, 'a3) rwset ->
    ('a2, ('a1, 'a2, 'a3) rwdata) env_t **)

let bundleref_wrap_rwset cR cSigma rEnv rl rs bundle rws =
  map0 rEnv (bundleref_wrap_rwdata cR cSigma rEnv rl rs bundle) rws

(** val bundleref_wrap_erwc :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> 'a1 -> 'a2 list
    -> ('a2, ('a1, 'a2, 'a3) rwdata) context -> ('a1, 'a2, 'a3) rwcircuit ->
    ('a1, 'a2, 'a3) rwcircuit **)

let bundleref_wrap_erwc cR cSigma rEnv rl rs bundle erwc0 =
  { canFire = (CBundleRef ((Pervasives.succ 0), rl, rs, bundle,
    Rwcircuit_canfire, erwc0.canFire)); regs =
    (bundleref_wrap_rwset cR cSigma rEnv rl rs bundle erwc0.regs) }

(** val bundleref_wrap_action_circuit :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> int -> 'a2 list
    -> ('a1, 'a2, 'a3) rwset -> ('a1, 'a2, 'a3) action_circuit -> 'a1 ->
    ('a1, 'a2, 'a3) action_circuit **)

let bundleref_wrap_action_circuit cR cSigma rEnv _ rs input rl rl_name =
  let bundle = ccreate rs (fun r0 _ -> getenv rEnv input r0) in
  { erwc = (bundleref_wrap_erwc cR cSigma rEnv rl_name rs bundle rl.erwc);
  retVal = rl.retVal }

(** val compile_scheduler_circuit :
    ('a4 -> int) -> ('a5 -> cExternalSignature) -> 'a4 env -> 'a2 show -> 'a3
    show -> (int -> ('a3, 'a4, 'a5, ('a3, 'a4, 'a5) rwdata) circuit -> ('a3,
    'a4, 'a5, ('a3, 'a4, 'a5) rwdata) circuit) -> ('a4, ('a3, 'a4, 'a5, ('a3,
    'a4, 'a5) rwdata) circuit) env_t -> ('a3 -> ('a1, 'a2, 'a4, 'a5) rule0)
    -> ('a3 -> bool) -> ('a1, 'a3) scheduler -> ('a3, 'a4, 'a5)
    scheduler_circuit -> ('a3, 'a4, 'a5) scheduler_circuit **)

let rec compile_scheduler_circuit cR cSigma rEnv show_var_t show_rule_name_t opt cr rules external0 s input =
  let compile_action0 = fun rl_name ->
    let rule1 = rules rl_name in
    let ft = rEnv.finite_keys in
    let rs = action_registers cR cSigma [] 0 (eqDec_FiniteType ft) rule1 in
    let (rl, _) =
      compile_action cR cSigma rEnv show_var_t opt cr [] 0 CtxEmpty rule1
        (adapter cR cSigma rEnv opt input)
    in
    let rl0 =
      if external0 rl_name
      then bundleref_wrap_action_circuit cR cSigma rEnv 0 rs input rl rl_name
      else rl
    in
    let acc = update_accumulated_rwset cR cSigma rEnv opt rl0.erwc.regs input
    in
    (rl0, acc)
  in
  (match s with
   | Done -> input
   | Cons (rl_name, s0) ->
     let (rl, acc) = compile_action0 rl_name in
     let will_fire =
       willFire_of_canFire cR cSigma rEnv show_rule_name_t opt rl_name
         rl.erwc input
     in
     let input0 =
       mux_rwsets cR cSigma rEnv opt
         (append (show_rule_name_t.show0 rl_name)
           ('_'::('o'::('u'::('t'::[]))))) will_fire acc input
     in
     compile_scheduler_circuit cR cSigma rEnv show_var_t show_rule_name_t opt
       cr rules external0 s0 input0
   | Try (rl_name, st, sf) ->
     let (rl, acc) = compile_action0 rl_name in
     let st0 =
       compile_scheduler_circuit cR cSigma rEnv show_var_t show_rule_name_t
         opt cr rules external0 st acc
     in
     let sf0 =
       compile_scheduler_circuit cR cSigma rEnv show_var_t show_rule_name_t
         opt cr rules external0 sf input
     in
     let will_fire =
       willFire_of_canFire cR cSigma rEnv show_rule_name_t opt rl_name
         rl.erwc input
     in
     mux_rwsets cR cSigma rEnv opt
       ('m'::('u'::('x'::('_'::('s'::('u'::('b'::('s'::('c'::('h'::('e'::('d'::('u'::('l'::('e'::('r'::('s'::[])))))))))))))))))
       will_fire st0 sf0
   | SPos (_, s0) ->
     compile_scheduler_circuit cR cSigma rEnv show_var_t show_rule_name_t opt
       cr rules external0 s0 input)

(** val commit_rwdata :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> (int -> ('a1, 'a2, 'a3,
    ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3)
    rwdata) circuit) -> int -> ('a1, 'a2, 'a3) rwdata -> ('a1, 'a2, 'a3,
    ('a1, 'a2, 'a3) rwdata) circuit **)

let commit_rwdata _ _ opt sz0 reg =
  CAnnot (sz0,
    ('c'::('o'::('m'::('m'::('i'::('t'::('_'::('w'::('r'::('i'::('t'::('e'::('1'::[]))))))))))))),
    (opt sz0 (CMux (sz0, reg.write1, reg.data1, reg.data0))))

(** val init_scheduler_rwdata :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> (int -> ('a1,
    'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2,
    'a3) rwdata) circuit) -> ('a2, ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
    circuit) env_t -> 'a2 -> ('a1, 'a2, 'a3) rwdata **)

let init_scheduler_rwdata cR _ rEnv opt cr idx =
  { read0 = (CAnnot ((Pervasives.succ 0),
    ('s'::('c'::('h'::('e'::('d'::('_'::('i'::('n'::('i'::('t'::('_'::('n'::('o'::('_'::('r'::('e'::('a'::('d'::('0'::[]))))))))))))))))))),
    (opt (Pervasives.succ 0) (CConst ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 false __)))))); read1 = (CAnnot
    ((Pervasives.succ 0),
    ('s'::('c'::('h'::('e'::('d'::('_'::('i'::('n'::('i'::('t'::('_'::('n'::('o'::('_'::('r'::('e'::('a'::('d'::('1'::[]))))))))))))))))))),
    (opt (Pervasives.succ 0) (CConst ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 false __)))))); write0 = (CAnnot
    ((Pervasives.succ 0),
    ('s'::('c'::('h'::('e'::('d'::('_'::('i'::('n'::('i'::('t'::('_'::('n'::('o'::('_'::('w'::('r'::('i'::('t'::('e'::('0'::[])))))))))))))))))))),
    (opt (Pervasives.succ 0) (CConst ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 false __)))))); write1 = (CAnnot
    ((Pervasives.succ 0),
    ('s'::('c'::('h'::('e'::('d'::('_'::('i'::('n'::('i'::('t'::('_'::('n'::('o'::('_'::('w'::('r'::('i'::('t'::('e'::('1'::[])))))))))))))))))))),
    (opt (Pervasives.succ 0) (CConst ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 false __)))))); data0 = (CAnnot ((cR idx),
    ('s'::('c'::('h'::('e'::('d'::('_'::('i'::('n'::('i'::('t'::('_'::('d'::('a'::('t'::('a'::('0'::('_'::('i'::('s'::('_'::('r'::('e'::('g'::[]))))))))))))))))))))))),
    (opt (cR idx) (getenv rEnv cr idx)))); data1 = (CAnnot ((cR idx),
    ('s'::('c'::('h'::('e'::('d'::('_'::('i'::('n'::('i'::('t'::('_'::('n'::('o'::('_'::('d'::('a'::('t'::('a'::('1'::[]))))))))))))))))))),
    (opt (cR idx) (CConst ((cR idx), (Bits.zero (cR idx))))))) }

(** val init_scheduler_circuit :
    ('a2 -> int) -> ('a3 -> cExternalSignature) -> 'a2 env -> (int -> ('a1,
    'a2, 'a3, ('a1, 'a2, 'a3) rwdata) circuit -> ('a1, 'a2, 'a3, ('a1, 'a2,
    'a3) rwdata) circuit) -> ('a2, ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) rwdata)
    circuit) env_t -> ('a1, 'a2, 'a3) scheduler_circuit **)

let init_scheduler_circuit cR cSigma rEnv opt cr =
  create rEnv (init_scheduler_rwdata cR cSigma rEnv opt cr)

type ('rule_name_t, 'reg_t, 'ext_fn_t) register_update_circuitry =
  ('reg_t, ('rule_name_t, 'reg_t, 'ext_fn_t, ('rule_name_t, 'reg_t,
  'ext_fn_t) rwdata) circuit) env_t

(** val compile_scheduler' :
    ('a4 -> int) -> ('a5 -> cExternalSignature) -> 'a4 env -> 'a2 show -> 'a3
    show -> (int -> ('a3, 'a4, 'a5, ('a3, 'a4, 'a5) rwdata) circuit -> ('a3,
    'a4, 'a5, ('a3, 'a4, 'a5) rwdata) circuit) -> ('a4, ('a3, 'a4, 'a5, ('a3,
    'a4, 'a5) rwdata) circuit) env_t -> ('a3 -> ('a1, 'a2, 'a4, 'a5) rule0)
    -> ('a3 -> bool) -> ('a1, 'a3) scheduler -> ('a3, 'a4, 'a5)
    register_update_circuitry **)

let compile_scheduler' cR cSigma rEnv show_var_t show_rule_name_t opt cr rules external0 s =
  let s0 =
    compile_scheduler_circuit cR cSigma rEnv show_var_t show_rule_name_t opt
      cr rules external0 s (init_scheduler_circuit cR cSigma rEnv opt cr)
  in
  map0 rEnv (fun k r0 -> commit_rwdata cR cSigma opt (cR k) r0) s0

(** val lower_R : ('a1 -> type0) -> 'a1 -> int **)

let lower_R r0 idx =
  type_sz (r0 idx)

(** val lower_Sigma : ('a1 -> externalSignature) -> 'a1 -> int _Sig **)

let lower_Sigma sigma fn =
  cSig_of_Sig (Pervasives.succ 0) (sigma fn)

(** val lower_unop :
    ('a3 -> type0) -> ('a4 -> externalSignature) -> lsig -> PrimTyped.fn1 ->
    ('a1, 'a2, 'a3, 'a4) action0 -> ('a1, 'a2, 'a3, 'a4) action0 **)

let lower_unop _ _ sig1 fn a =
  match fn with
  | PrimTyped.Display fn0 ->
    Unop0 (sig1, (PrimTyped.Lowered (PrimTyped.DisplayBits fn0)), a)
  | PrimTyped.Conv (tau, fn0) ->
    (match fn0 with
     | PrimTyped.Ignore ->
       Unop0 (sig1, (PrimTyped.Lowered (PrimTyped.IgnoreBits
         (type_sz
           (vect_hd 0
             (Obj.magic
               (PrimSignatures.coq_Sigma1 (PrimTyped.Conv (tau,
                 PrimTyped.Ignore))).argSigs))))), a)
     | _ -> a)
  | PrimTyped.Bits1 fn0 -> Unop0 (sig1, fn0, a)
  | PrimTyped.Struct1 (sig2, f) ->
    Unop0 (sig1, (PrimTyped.coq_GetFieldBits sig2 f), a)
  | PrimTyped.Array1 (sig2, idx) ->
    Unop0 (sig1, (PrimTyped.coq_GetElementBits sig2 idx), a)

(** val lower_binop :
    ('a3 -> type0) -> ('a4 -> externalSignature) -> lsig -> PrimTyped.fn2 ->
    ('a1, 'a2, 'a3, 'a4) action0 -> ('a1, 'a2, 'a3, 'a4) action0 -> ('a1,
    'a2, 'a3, 'a4) action0 **)

let lower_binop _ _ sig1 fn a1 a2 =
  match fn with
  | PrimTyped.Eq (tau, negate) ->
    Binop0 (sig1, (PrimTyped.EqBits ((type_sz tau), negate)), a1, a2)
  | PrimTyped.Bits2 fn0 -> Binop0 (sig1, fn0, a1, a2)
  | PrimTyped.Struct2 (sig2, f) ->
    Binop0 (sig1, (PrimTyped.coq_SubstFieldBits sig2 f), a1, a2)
  | PrimTyped.Array2 (sig2, idx) ->
    Binop0 (sig1, (PrimTyped.coq_SubstElementBits sig2 idx), a1, a2)

(** val lower_member :
    'a1 -> type0 -> ('a1 * type0) list -> ('a1 * type0) member -> int member **)

let lower_member k tau sig1 m =
  member_map (fun k_tau -> type_sz (snd k_tau)) (k, tau) sig1 m

(** val lower_args' :
    ('a4 -> type0) -> ('a5 -> externalSignature) -> ('a2 tsig -> type0 ->
    ('a1, 'a2, 'a3, 'a4, 'a5) action -> ('a1, 'a2, 'a4, 'a5) action0) -> 'a2
    tsig -> ('a2 * type0) list -> ('a2 * type0, ('a1, 'a2, 'a3, 'a4, 'a5)
    action) context -> (int, 'a2 * ('a1, 'a2, 'a4, 'a5) action0) context **)

let lower_args' _ _ lower_action0 sig1 argspec args =
  cmap (fun k_tau -> type_sz (snd k_tau)) (fun k_tau a -> ((fst k_tau),
    (lower_action0 sig1 (snd k_tau) a))) argspec args

(** val lower_action :
    ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a2 tsig -> type0 ->
    ('a1, 'a2, 'a3, 'a4, 'a5) action -> ('a1, 'a2, 'a4, 'a5) action0 **)

let rec lower_action r0 sigma _ _ = function
| Fail (sig1, tau) -> Fail0 ((lsig_of_tsig sig1), (type_sz tau))
| Var (sig1, k, tau0, m) ->
  Var0 ((lsig_of_tsig sig1), k, (type_sz tau0), (lower_member k tau0 sig1 m))
| Const (sig1, tau0, cst) ->
  Const0 ((lsig_of_tsig sig1), (type_sz tau0), (bits_of_value tau0 cst))
| Assign (sig1, k, tau0, m, ex) ->
  Assign0 ((lsig_of_tsig sig1), k, (type_sz tau0),
    (lower_member k tau0 sig1 m), (lower_action r0 sigma sig1 tau0 ex))
| Seq (sig1, tau0, r1, r2) ->
  Seq0 ((lsig_of_tsig sig1), (type_sz tau0),
    (lower_action r0 sigma sig1 (Bits_t 0) r1),
    (lower_action r0 sigma sig1 tau0 r2))
| Bind (sig1, tau0, tau', var, ex, body) ->
  Bind0 ((lsig_of_tsig sig1), var, (type_sz tau0), (type_sz tau'),
    (lower_action r0 sigma sig1 tau0 ex),
    (lower_action r0 sigma ((var, tau0) :: sig1) tau' body))
| If (sig1, tau0, cond, tbranch, fbranch) ->
  If0 ((lsig_of_tsig sig1), (type_sz tau0),
    (lower_action r0 sigma sig1 (Bits_t (Pervasives.succ 0)) cond),
    (lower_action r0 sigma sig1 tau0 tbranch),
    (lower_action r0 sigma sig1 tau0 fbranch))
| Read (sig1, p, idx) -> Read0 ((lsig_of_tsig sig1), p, idx)
| Write (sig1, p, idx, val0) ->
  Write0 ((lsig_of_tsig sig1), p, idx,
    (lower_action r0 sigma sig1 (r0 idx) val0))
| Unop (sig1, fn, a0) ->
  lower_unop r0 sigma (lsig_of_tsig sig1) fn
    (lower_action r0 sigma sig1
      (vect_hd 0 (Obj.magic (PrimSignatures.coq_Sigma1 fn).argSigs)) a0)
| Binop (sig1, fn, a1, a2) ->
  lower_binop r0 sigma (lsig_of_tsig sig1) fn
    (lower_action r0 sigma sig1
      (vect_hd (Pervasives.succ 0)
        (Obj.magic (PrimSignatures.coq_Sigma2 fn).argSigs)) a1)
    (lower_action r0 sigma sig1
      (vect_hd 0
        (Obj.magic vect_tl (Pervasives.succ 0)
          (PrimSignatures.coq_Sigma2 fn).argSigs)) a2)
| ExternalCall (sig1, fn, a0) ->
  ExternalCall0 ((lsig_of_tsig sig1), fn,
    (lower_action r0 sigma sig1 (vect_hd 0 (Obj.magic (sigma fn).argSigs)) a0))
| InternalCall (sig1, tau0, _, argspec, args, body) ->
  internalCall (lower_R r0) (lower_Sigma sigma) (type_sz tau0)
    (lsig_of_tsig sig1)
    (map (fun k_tau -> type_sz (snd k_tau)) (rev argspec))
    (lower_args' r0 sigma (lower_action r0 sigma) sig1 (rev argspec) args)
    (lower_action r0 sigma (rev argspec) tau0 body)
| APos (sig1, tau0, p, a0) ->
  APos0 ((lsig_of_tsig sig1), (type_sz tau0), p,
    (lower_action r0 sigma sig1 tau0 a0))

(** val compile_scheduler :
    ('a5 -> type0) -> ('a6 -> externalSignature) -> 'a5 finiteType -> 'a2
    show -> 'a4 show -> (int -> ('a4, 'a5, 'a6, ('a4, 'a5, 'a6) rwdata)
    circuit -> ('a4, 'a5, 'a6, ('a4, 'a5, 'a6) rwdata) circuit) -> ('a4 ->
    ('a1, 'a2, 'a3, 'a5, 'a6) rule) -> ('a4 -> bool) -> ('a1, 'a4) scheduler
    -> ('a4, 'a5, 'a6) register_update_circuitry **)

let compile_scheduler r0 sigma finiteType_reg_t show_var_t show_rule_name_t opt rules external0 s =
  let cr =
    create (contextEnv finiteType_reg_t)
      (readRegisters (lower_R r0) (lower_Sigma sigma))
  in
  compile_scheduler' (lower_R r0) (lower_Sigma sigma)
    (contextEnv finiteType_reg_t) show_var_t show_rule_name_t opt cr
    (fun rl -> lower_action r0 sigma [] (Bits_t 0) (rules rl)) external0 s

type ext_fn_rtl_spec = { efr_name : char list; efr_internal : bool }

type ext_fn_sim_spec = { efs_name : char list; efs_method : bool }

(** val lift_empty : __ -> 'a1 **)

let lift_empty _ =
  assert false (* absurd case *)

(** val lift_self : ('a1, 'a1) lift **)

let lift_self fn =
  fn

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

(** val maybe : type0 -> type0 struct_sig' **)

let maybe tau =
  { struct_name =
    (append ('m'::('a'::('y'::('b'::('e'::('_'::[])))))) (type_id tau));
    struct_fields = ((('v'::('a'::('l'::('i'::('d'::[]))))), (Bits_t
    (Pervasives.succ 0))) :: ((('d'::('a'::('t'::('a'::[])))), tau) :: [])) }

(** val valid :
    type0 -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, 'a2) uaction)
    internalFunction **)

let valid tau =
  { int_name = ('v'::('a'::('l'::('i'::('d'::[]))))); int_argspec =
    ((prod_of_argsig { arg_name = ('x'::[]); arg_type = tau }) :: []);
    int_retSig = (Struct_t (maybe tau)); int_body = (USugar (UStructInit
    ((maybe tau),
    (app ((('v'::('a'::('l'::('i'::('d'::[]))))), (USugar (UConstBits
      ((Pervasives.succ 0), (Obj.magic vect_cons 0 true __))))) :: [])
      ((('d'::('a'::('t'::('a'::[])))), (UVar ('x'::[]))) :: []))))) }

(** val invalid :
    type0 -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, 'a2) uaction)
    internalFunction **)

let invalid tau =
  { int_name = ('i'::('n'::('v'::('a'::('l'::('i'::('d'::[])))))));
    int_argspec = []; int_retSig = (Struct_t (maybe tau)); int_body = (USugar
    (UStructInit ((maybe tau), ((('v'::('a'::('l'::('i'::('d'::[]))))),
    (USugar (UConstBits ((Pervasives.succ 0),
    (Obj.magic vect_cons 0 false __))))) :: [])))) }

module type Fifo =
 sig
  val coq_T : type0
 end

module Fifo1 =
 functor (Coq_f:Fifo) ->
 struct
  type reg_t =
  | Coq_data0
  | Coq_valid0

  (** val reg_t_rect : 'a1 -> 'a1 -> reg_t -> 'a1 **)

  let reg_t_rect f f0 = function
  | Coq_data0 -> f
  | Coq_valid0 -> f0

  (** val reg_t_rec : 'a1 -> 'a1 -> reg_t -> 'a1 **)

  let reg_t_rec f f0 = function
  | Coq_data0 -> f
  | Coq_valid0 -> f0

  (** val coq_R : reg_t -> type0 **)

  let coq_R = function
  | Coq_data0 -> Coq_f.coq_T
  | Coq_valid0 -> Bits_t (Pervasives.succ 0)

  (** val r : reg_t -> type_denote **)

  let r = function
  | Coq_data0 ->
    value_of_bits (coq_R Coq_data0) (Bits.zero (type_sz (coq_R Coq_data0)))
  | Coq_valid0 -> Bits.zero (Pervasives.succ 0)

  (** val name_reg : reg_t -> char list **)

  let name_reg = function
  | Coq_data0 -> 'd'::('a'::('t'::('a'::('0'::[]))))
  | Coq_valid0 -> 'v'::('a'::('l'::('i'::('d'::('0'::[])))))

  (** val can_enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let can_enq =
    { int_name = ('c'::('a'::('n'::('_'::('e'::('n'::('q'::[])))))));
      int_argspec = []; int_retSig = (Bits_t (Pervasives.succ 0)); int_body =
      (UUnop ((PrimUntyped.UBits1 PrimUntyped.UNot), (URead (P1,
      Coq_valid0)))) }

  (** val enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let enq =
    { int_name = ('e'::('n'::('q'::[]))); int_argspec =
      ((prod_of_argsig { arg_name = ('d'::('a'::('t'::('a'::[]))));
         arg_type = Coq_f.coq_T }) :: []); int_retSig = (Bits_t 0);
      int_body = (USeq ((USeq ((UIf ((UUnop ((PrimUntyped.UBits1
      PrimUntyped.UNot), (USugar (UCallModule ({ finite_index = (fun h ->
      match Obj.magic h with
      | Coq_data0 -> 0
      | Coq_valid0 -> Pervasives.succ 0); finite_elements =
      ((Obj.magic Coq_data0) :: ((Obj.magic Coq_valid0) :: [])) },
      (Obj.magic id), (Obj.magic __), (Obj.magic can_enq), []))))), (UFail
      (Bits_t 0)), (USugar (UConstBits (0, (Obj.magic __)))))), (UWrite (P1,
      Coq_data0, (UVar ('d'::('a'::('t'::('a'::[]))))))))), (UWrite (P1,
      Coq_valid0, (USugar (UConstBits ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 true __)))))))) }

  (** val can_deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let can_deq =
    { int_name = ('c'::('a'::('n'::('_'::('d'::('e'::('q'::[])))))));
      int_argspec = []; int_retSig = (Bits_t (Pervasives.succ 0)); int_body =
      (URead (P0, Coq_valid0)) }

  (** val peek :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let peek =
    { int_name = ('p'::('e'::('e'::('k'::[])))); int_argspec = [];
      int_retSig = (Struct_t (maybe Coq_f.coq_T)); int_body = (UIf ((USugar
      (UCallModule ({ finite_index = (fun h ->
      match Obj.magic h with
      | Coq_data0 -> 0
      | Coq_valid0 -> Pervasives.succ 0); finite_elements =
      ((Obj.magic Coq_data0) :: ((Obj.magic Coq_valid0) :: [])) },
      (Obj.magic id), (Obj.magic __), (Obj.magic can_deq), []))), (USugar
      (UCallModule ({ finite_index = (fun h ->
      match Obj.magic h with
      | Coq_data0 -> 0
      | Coq_valid0 -> Pervasives.succ 0); finite_elements =
      ((Obj.magic Coq_data0) :: ((Obj.magic Coq_valid0) :: [])) },
      (Obj.magic id), (Obj.magic __), (valid Coq_f.coq_T), ((URead (P0,
      Coq_data0)) :: [])))), (USugar (UCallModule ({ finite_index = (fun h ->
      match Obj.magic h with
      | Coq_data0 -> 0
      | Coq_valid0 -> Pervasives.succ 0); finite_elements =
      ((Obj.magic Coq_data0) :: ((Obj.magic Coq_valid0) :: [])) },
      (Obj.magic id), (Obj.magic __), (invalid Coq_f.coq_T), []))))) }

  (** val deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let deq =
    { int_name = ('d'::('e'::('q'::[]))); int_argspec = []; int_retSig =
      Coq_f.coq_T; int_body = (USeq ((USeq ((UIf ((UUnop ((PrimUntyped.UBits1
      PrimUntyped.UNot), (USugar (UCallModule ({ finite_index = (fun h ->
      match Obj.magic h with
      | Coq_data0 -> 0
      | Coq_valid0 -> Pervasives.succ 0); finite_elements =
      ((Obj.magic Coq_data0) :: ((Obj.magic Coq_valid0) :: [])) },
      (Obj.magic id), (Obj.magic __), (Obj.magic can_deq), []))))), (UFail
      (Bits_t 0)), (USugar (UConstBits (0, (Obj.magic __)))))), (UWrite (P0,
      Coq_valid0, (USugar (UConstBits ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 false __)))))))), (URead (P0, Coq_data0)))) }

  (** val coq_FiniteType_reg_t : reg_t finiteType **)

  let coq_FiniteType_reg_t =
    { finite_index = (fun h ->
      match h with
      | Coq_data0 -> 0
      | Coq_valid0 -> Pervasives.succ 0); finite_elements =
      (Coq_data0 :: (Coq_valid0 :: [])) }
 end

module Fifo1Bypass =
 functor (Coq_f:Fifo) ->
 struct
  type reg_t =
  | Coq_data0
  | Coq_valid0

  (** val reg_t_rect : 'a1 -> 'a1 -> reg_t -> 'a1 **)

  let reg_t_rect f f0 = function
  | Coq_data0 -> f
  | Coq_valid0 -> f0

  (** val reg_t_rec : 'a1 -> 'a1 -> reg_t -> 'a1 **)

  let reg_t_rec f f0 = function
  | Coq_data0 -> f
  | Coq_valid0 -> f0

  (** val coq_R : reg_t -> type0 **)

  let coq_R = function
  | Coq_data0 -> Coq_f.coq_T
  | Coq_valid0 -> Bits_t (Pervasives.succ 0)

  (** val r : reg_t -> type_denote **)

  let r = function
  | Coq_data0 ->
    value_of_bits (coq_R Coq_data0) (Bits.zero (type_sz (coq_R Coq_data0)))
  | Coq_valid0 -> Bits.zero (Pervasives.succ 0)

  (** val name_reg : reg_t -> char list **)

  let name_reg = function
  | Coq_data0 -> 'd'::('a'::('t'::('a'::('0'::[]))))
  | Coq_valid0 -> 'v'::('a'::('l'::('i'::('d'::('0'::[])))))

  (** val can_enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let can_enq =
    { int_name = ('c'::('a'::('n'::('_'::('e'::('n'::('q'::[])))))));
      int_argspec = []; int_retSig = (Bits_t (Pervasives.succ 0)); int_body =
      (UUnop ((PrimUntyped.UBits1 PrimUntyped.UNot), (URead (P0,
      Coq_valid0)))) }

  (** val enq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let enq =
    { int_name = ('e'::('n'::('q'::[]))); int_argspec =
      ((prod_of_argsig { arg_name = ('d'::('a'::('t'::('a'::[]))));
         arg_type = Coq_f.coq_T }) :: []); int_retSig = (Bits_t 0);
      int_body = (USeq ((USeq ((UIf ((UUnop ((PrimUntyped.UBits1
      PrimUntyped.UNot), (USugar (UCallModule ({ finite_index = (fun h ->
      match Obj.magic h with
      | Coq_data0 -> 0
      | Coq_valid0 -> Pervasives.succ 0); finite_elements =
      ((Obj.magic Coq_data0) :: ((Obj.magic Coq_valid0) :: [])) },
      (Obj.magic id), (Obj.magic __), (Obj.magic can_enq), []))))), (UFail
      (Bits_t 0)), (USugar (UConstBits (0, (Obj.magic __)))))), (UWrite (P0,
      Coq_data0, (UVar ('d'::('a'::('t'::('a'::[]))))))))), (UWrite (P0,
      Coq_valid0, (USugar (UConstBits ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 true __)))))))) }

  (** val can_deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let can_deq =
    { int_name = ('c'::('a'::('n'::('_'::('d'::('e'::('q'::[])))))));
      int_argspec = []; int_retSig = (Bits_t (Pervasives.succ 0)); int_body =
      (URead (P1, Coq_valid0)) }

  (** val peek :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let peek =
    { int_name = ('p'::('e'::('e'::('k'::[])))); int_argspec = [];
      int_retSig = (Struct_t (maybe Coq_f.coq_T)); int_body = (UIf ((USugar
      (UCallModule ({ finite_index = (fun h ->
      match Obj.magic h with
      | Coq_data0 -> 0
      | Coq_valid0 -> Pervasives.succ 0); finite_elements =
      ((Obj.magic Coq_data0) :: ((Obj.magic Coq_valid0) :: [])) },
      (Obj.magic id), (Obj.magic __), (Obj.magic can_deq), []))), (USugar
      (UCallModule ({ finite_index = (fun h ->
      match Obj.magic h with
      | Coq_data0 -> 0
      | Coq_valid0 -> Pervasives.succ 0); finite_elements =
      ((Obj.magic Coq_data0) :: ((Obj.magic Coq_valid0) :: [])) },
      (Obj.magic id), (Obj.magic __), (valid Coq_f.coq_T), ((URead (P1,
      Coq_data0)) :: [])))), (USugar (UCallModule ({ finite_index = (fun h ->
      match Obj.magic h with
      | Coq_data0 -> 0
      | Coq_valid0 -> Pervasives.succ 0); finite_elements =
      ((Obj.magic Coq_data0) :: ((Obj.magic Coq_valid0) :: [])) },
      (Obj.magic id), (Obj.magic __), (invalid Coq_f.coq_T), []))))) }

  (** val deq :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let deq =
    { int_name = ('d'::('e'::('q'::[]))); int_argspec = []; int_retSig =
      Coq_f.coq_T; int_body = (USeq ((USeq ((UIf ((UUnop ((PrimUntyped.UBits1
      PrimUntyped.UNot), (USugar (UCallModule ({ finite_index = (fun h ->
      match Obj.magic h with
      | Coq_data0 -> 0
      | Coq_valid0 -> Pervasives.succ 0); finite_elements =
      ((Obj.magic Coq_data0) :: ((Obj.magic Coq_valid0) :: [])) },
      (Obj.magic id), (Obj.magic __), (Obj.magic can_deq), []))))), (UFail
      (Bits_t 0)), (USugar (UConstBits (0, (Obj.magic __)))))), (UWrite (P1,
      Coq_valid0, (USugar (UConstBits ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 false __)))))))), (URead (P1, Coq_data0)))) }

  (** val coq_FiniteType_reg_t : reg_t finiteType **)

  let coq_FiniteType_reg_t =
    { finite_index = (fun h ->
      match h with
      | Coq_data0 -> 0
      | Coq_valid0 -> Pervasives.succ 0); finite_elements =
      (Coq_data0 :: (Coq_valid0 :: [])) }
 end

module type RfPow2_sig =
 sig
  val idx_sz : int

  val coq_T : type0

  val init : type_denote

  val read_style : var_t switch_style

  val write_style : var_t switch_style
 end

module RfPow2 =
 functor (Coq_s:RfPow2_sig) ->
 struct
  (** val sz : int **)

  let sz =
    pow2 Coq_s.idx_sz

  type reg_t =
  | Coq_rData of index

  (** val reg_t_rect : (index -> 'a1) -> reg_t -> 'a1 **)

  let reg_t_rect f = function
  | Coq_rData x -> f x

  (** val reg_t_rec : (index -> 'a1) -> reg_t -> 'a1 **)

  let reg_t_rec f = function
  | Coq_rData x -> f x

  (** val finite_rf_reg : reg_t finiteType **)

  let finite_rf_reg =
    let f = finiteType_index sz in
    let { finite_index = finite_index0; finite_elements =
      finite_elements0 } = f
    in
    { finite_index = (fun r0 -> let Coq_rData idx = r0 in finite_index0 idx);
    finite_elements = (map (fun i -> Coq_rData i) finite_elements0) }

  (** val coq_R : reg_t -> type0 **)

  let coq_R _ =
    Coq_s.coq_T

  (** val r : reg_t -> type_denote **)

  let r _ =
    Coq_s.init

  (** val name_reg : reg_t -> char list **)

  let name_reg = function
  | Coq_rData n0 ->
    append ('r'::('D'::('a'::('t'::('a'::('_'::[]))))))
      ((show_index sz).show0 n0)

  (** val read_0 :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let read_0 =
    { int_name = ('r'::('e'::('a'::('d'::('_'::('0'::[])))))); int_argspec =
      ((prod_of_argsig { arg_name = ('i'::('d'::('x'::[]))); arg_type =
         (Bits_t Coq_s.idx_sz) }) :: []); int_retSig = Coq_s.coq_T;
      int_body =
      (uCompleteSwitch Coq_s.read_style Coq_s.idx_sz ('i'::('d'::('x'::[])))
        (fun idx -> URead (P0, (Coq_rData idx)))) }

  (** val write_0 :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let write_0 =
    { int_name = ('w'::('r'::('i'::('t'::('e'::('_'::('0'::[])))))));
      int_argspec =
      (app
        ((prod_of_argsig { arg_name = ('i'::('d'::('x'::[]))); arg_type =
           (Bits_t Coq_s.idx_sz) }) :: [])
        ((prod_of_argsig { arg_name = ('v'::('a'::('l'::[]))); arg_type =
           Coq_s.coq_T }) :: [])); int_retSig = (Bits_t 0); int_body =
      (uCompleteSwitch Coq_s.write_style Coq_s.idx_sz ('i'::('d'::('x'::[])))
        (fun idx -> UWrite (P0, (Coq_rData idx), (UVar
        ('v'::('a'::('l'::[]))))))) }

  (** val read_1 :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let read_1 =
    { int_name = ('r'::('e'::('a'::('d'::('_'::('1'::[])))))); int_argspec =
      ((prod_of_argsig { arg_name = ('i'::('d'::('x'::[]))); arg_type =
         (Bits_t Coq_s.idx_sz) }) :: []); int_retSig = Coq_s.coq_T;
      int_body =
      (uCompleteSwitch Coq_s.read_style Coq_s.idx_sz ('i'::('d'::('x'::[])))
        (fun idx -> URead (P1, (Coq_rData idx)))) }

  (** val write_1 :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let write_1 =
    { int_name = ('w'::('r'::('i'::('t'::('e'::('_'::('1'::[])))))));
      int_argspec =
      (app
        ((prod_of_argsig { arg_name = ('i'::('d'::('x'::[]))); arg_type =
           (Bits_t Coq_s.idx_sz) }) :: [])
        ((prod_of_argsig { arg_name = ('v'::('a'::('l'::[]))); arg_type =
           Coq_s.coq_T }) :: [])); int_retSig = (Bits_t 0); int_body =
      (uCompleteSwitch Coq_s.write_style Coq_s.idx_sz ('i'::('d'::('x'::[])))
        (fun idx -> UWrite (P1, (Coq_rData idx), (UVar
        ('v'::('a'::('l'::[]))))))) }
 end

(** val signExtend :
    int -> int -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __)
    uaction) internalFunction **)

let signExtend n0 m =
  { int_name =
    ('s'::('i'::('g'::('n'::('E'::('x'::('t'::('e'::('n'::('d'::[]))))))))));
    int_argspec =
    ((prod_of_argsig { arg_name = ('a'::('r'::('g'::[]))); arg_type = (Bits_t
       n0) }) :: []); int_retSig = (Bits_t (add m n0)); int_body = (UUnop
    ((PrimUntyped.UBits1 (PrimUntyped.USExt (add m n0))), (UVar
    ('a'::('r'::('g'::[])))))) }

(** val funct3_ADD :
    (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t **)

let funct3_ADD =
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
    (vect_cons (Pervasives.succ 0) false (Obj.magic vect_cons 0 false __))

(** val funct7_ADD :
    (bool, (bool, (bool, (bool, (bool, (bool, (bool, __) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t **)

let funct7_ADD =
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))

(** val funct3_SLL :
    (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t **)

let funct3_SLL =
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
    (vect_cons (Pervasives.succ 0) false (Obj.magic vect_cons 0 false __))

(** val funct3_SLT :
    (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t **)

let funct3_SLT =
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
    (vect_cons (Pervasives.succ 0) true (Obj.magic vect_cons 0 false __))

(** val funct3_SLTU :
    (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t **)

let funct3_SLTU =
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
    (vect_cons (Pervasives.succ 0) true (Obj.magic vect_cons 0 false __))

(** val funct3_XOR :
    (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t **)

let funct3_XOR =
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
    (vect_cons (Pervasives.succ 0) false (Obj.magic vect_cons 0 true __))

(** val funct3_SRL :
    (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t **)

let funct3_SRL =
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
    (vect_cons (Pervasives.succ 0) false (Obj.magic vect_cons 0 true __))

(** val funct3_OR :
    (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t **)

let funct3_OR =
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
    (vect_cons (Pervasives.succ 0) true (Obj.magic vect_cons 0 true __))

(** val funct3_AND :
    (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t **)

let funct3_AND =
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
    (vect_cons (Pervasives.succ 0) true (Obj.magic vect_cons 0 true __))

(** val opcode_BRANCH :
    (bool, (bool, (bool, (bool, (bool, (bool, (bool, __) vect_cons_t)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t **)

let opcode_BRANCH =
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 true __))))))

(** val funct3_BEQ :
    (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t **)

let funct3_BEQ =
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
    (vect_cons (Pervasives.succ 0) false (Obj.magic vect_cons 0 false __))

(** val funct3_BNE :
    (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t **)

let funct3_BNE =
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
    (vect_cons (Pervasives.succ 0) false (Obj.magic vect_cons 0 false __))

(** val funct3_BLT :
    (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t **)

let funct3_BLT =
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
    (vect_cons (Pervasives.succ 0) false (Obj.magic vect_cons 0 true __))

(** val funct3_BGE :
    (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t **)

let funct3_BGE =
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
    (vect_cons (Pervasives.succ 0) false (Obj.magic vect_cons 0 true __))

(** val funct3_BLTU :
    (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t **)

let funct3_BLTU =
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
    (vect_cons (Pervasives.succ 0) true (Obj.magic vect_cons 0 true __))

(** val funct3_BGEU :
    (bool, (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t **)

let funct3_BGEU =
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
    (vect_cons (Pervasives.succ 0) true (Obj.magic vect_cons 0 true __))

module type Scoreboard_sig =
 sig
  val idx_sz : int

  val maxScore : int
 end

(** val write_style0 : var_t switch_style **)

let write_style0 =
  SequentialSwitchTt

(** val read_style0 : int -> var_t switch_style **)

let read_style0 nbits =
  OrTreeSwitch nbits

module Scoreboard =
 functor (Coq_s:Scoreboard_sig) ->
 struct
  (** val sz : int **)

  let sz =
    Coq_s.idx_sz

  (** val logScore : int **)

  let logScore =
    Nat.log2_up Coq_s.maxScore

  module RfParams =
   struct
    (** val idx_sz : int **)

    let idx_sz =
      sz

    (** val coq_T : type0 **)

    let coq_T =
      Bits_t logScore

    (** val init : bool vect **)

    let init =
      vect_const logScore false

    (** val read_style : var_t switch_style **)

    let read_style =
      read_style0 logScore

    (** val write_style : var_t switch_style **)

    let write_style =
      write_style0
   end

  module Rf = RfPow2(RfParams)

  type reg_t =
  | Scores of Rf.reg_t

  (** val reg_t_rect : (Rf.reg_t -> 'a1) -> reg_t -> 'a1 **)

  let reg_t_rect f = function
  | Scores x -> f x

  (** val reg_t_rec : (Rf.reg_t -> 'a1) -> reg_t -> 'a1 **)

  let reg_t_rec f = function
  | Scores x -> f x

  (** val coq_R : reg_t -> type0 **)

  let coq_R = function
  | Scores n0 -> Rf.coq_R n0

  (** val r : reg_t -> type_denote **)

  let r = function
  | Scores n0 -> Rf.r n0

  (** val name_reg : reg_t -> char list **)

  let name_reg = function
  | Scores n0 -> append ('r'::('f'::[])) (Rf.name_reg n0)

  (** val sat_incr :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let sat_incr =
    { int_name = ('s'::('a'::('t'::('_'::('i'::('n'::('c'::('r'::[]))))))));
      int_argspec =
      ((prod_of_argsig { arg_name = ('a'::[]); arg_type = (Bits_t logScore) }) :: []);
      int_retSig = (Bits_t logScore); int_body = (UBinop ((PrimUntyped.UBits2
      PrimUntyped.UPlus), (UVar ('a'::[])), (USugar (UConstBits (logScore,
      (Bits.of_nat logScore (Pervasives.succ 0))))))) }

  (** val sat_decr :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let sat_decr =
    { int_name = ('s'::('a'::('t'::('_'::('d'::('e'::('c'::('r'::[]))))))));
      int_argspec =
      ((prod_of_argsig { arg_name = ('a'::[]); arg_type = (Bits_t logScore) }) :: []);
      int_retSig = (Bits_t logScore); int_body = (UBinop ((PrimUntyped.UBits2
      PrimUntyped.UMinus), (UVar ('a'::[])), (USugar (UConstBits (logScore,
      (Bits.of_N logScore 1)))))) }

  (** val finite_rf_reg : Rf.reg_t finiteType **)

  let finite_rf_reg =
    let f = finiteType_index Rf.sz in
    let { finite_index = finite_index0; finite_elements =
      finite_elements0 } = f
    in
    { finite_index = (fun r0 ->
    let Rf.Coq_rData idx = r0 in finite_index0 idx); finite_elements =
    (map (fun i -> Rf.Coq_rData i) finite_elements0) }

  (** val finite_reg : reg_t finiteType **)

  let finite_reg =
    let { finite_index = finite_index0; finite_elements =
      finite_elements0 } = finite_rf_reg
    in
    { finite_index = (fun r0 -> let Scores idx = r0 in finite_index0 idx);
    finite_elements = (map (fun i -> Scores i) finite_elements0) }

  (** val insert :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let insert =
    { int_name = ('i'::('n'::('s'::('e'::('r'::('t'::[])))))); int_argspec =
      ((prod_of_argsig { arg_name = ('i'::('d'::('x'::[]))); arg_type =
         (Bits_t sz) }) :: []); int_retSig = (Bits_t 0); int_body = (UBind
      (('o'::('l'::('d'::('_'::('s'::('c'::('o'::('r'::('e'::[]))))))))),
      (USugar (UCallModule ((Obj.magic finite_rf_reg),
      (Obj.magic (fun x -> Scores x)), (Obj.magic __), (Obj.magic Rf.read_1),
      ((UVar ('i'::('d'::('x'::[])))) :: [])))), (UBind
      (('n'::('e'::('w'::('_'::('s'::('c'::('o'::('r'::('e'::[]))))))))),
      (USugar (UCallModule ((Obj.magic finite_reg), (Obj.magic id),
      (Obj.magic __), (Obj.magic sat_incr), ((UVar
      ('o'::('l'::('d'::('_'::('s'::('c'::('o'::('r'::('e'::[])))))))))) :: [])))),
      (USugar (UCallModule ((Obj.magic finite_rf_reg),
      (Obj.magic (fun x -> Scores x)), (Obj.magic __),
      (Obj.magic Rf.write_1),
      (app ((UVar ('i'::('d'::('x'::[])))) :: []) ((UVar
        ('n'::('e'::('w'::('_'::('s'::('c'::('o'::('r'::('e'::[])))))))))) :: []))))))))) }

  (** val remove :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let remove =
    { int_name = ('r'::('e'::('m'::('o'::('v'::('e'::[])))))); int_argspec =
      ((prod_of_argsig { arg_name = ('i'::('d'::('x'::[]))); arg_type =
         (Bits_t sz) }) :: []); int_retSig = (Bits_t 0); int_body = (UBind
      (('o'::('l'::('d'::('_'::('s'::('c'::('o'::('r'::('e'::[]))))))))),
      (USugar (UCallModule ((Obj.magic finite_rf_reg),
      (Obj.magic (fun x -> Scores x)), (Obj.magic __), (Obj.magic Rf.read_0),
      ((UVar ('i'::('d'::('x'::[])))) :: [])))), (UBind
      (('n'::('e'::('w'::('_'::('s'::('c'::('o'::('r'::('e'::[]))))))))),
      (USugar (UCallModule ((Obj.magic finite_reg), (Obj.magic id),
      (Obj.magic __), (Obj.magic sat_decr), ((UVar
      ('o'::('l'::('d'::('_'::('s'::('c'::('o'::('r'::('e'::[])))))))))) :: [])))),
      (USugar (UCallModule ((Obj.magic finite_rf_reg),
      (Obj.magic (fun x -> Scores x)), (Obj.magic __),
      (Obj.magic Rf.write_0),
      (app ((UVar ('i'::('d'::('x'::[])))) :: []) ((UVar
        ('n'::('e'::('w'::('_'::('s'::('c'::('o'::('r'::('e'::[])))))))))) :: []))))))))) }

  (** val search :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let search =
    { int_name = ('s'::('e'::('a'::('r'::('c'::('h'::[])))))); int_argspec =
      ((prod_of_argsig { arg_name = ('i'::('d'::('x'::[]))); arg_type =
         (Bits_t sz) }) :: []); int_retSig = (Bits_t logScore); int_body =
      (USugar (UCallModule ((Obj.magic finite_rf_reg),
      (Obj.magic (fun x -> Scores x)), (Obj.magic __), (Obj.magic Rf.read_1),
      ((UVar ('i'::('d'::('x'::[])))) :: [])))) }
 end

module ShadowStackF =
 struct
  (** val capacity : int **)

  let capacity =
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))

  type _reg_t =
  | Coq_size
  | Coq_stack of index

  (** val _reg_t_rect : 'a1 -> (index -> 'a1) -> _reg_t -> 'a1 **)

  let _reg_t_rect f f0 = function
  | Coq_size -> f
  | Coq_stack x -> f0 x

  (** val _reg_t_rec : 'a1 -> (index -> 'a1) -> _reg_t -> 'a1 **)

  let _reg_t_rec f f0 = function
  | Coq_size -> f
  | Coq_stack x -> f0 x

  type reg_t = _reg_t

  (** val coq_R : _reg_t -> type0 **)

  let coq_R = function
  | Coq_size -> Bits_t (Nat.log2_up (add capacity (Pervasives.succ 0)))
  | Coq_stack _ ->
    Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))))))))))))))))))))))))))))))

  (** val r : _reg_t -> type_denote **)

  let r = function
  | Coq_size -> Bits.zero (Nat.log2_up (add capacity (Pervasives.succ 0)))
  | Coq_stack _ ->
    Bits.zero (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))))))))))))))))))))))))))))))

  (** val read_vect_sequential :
      char list -> (pos_t, var_t, fn_name_t, reg_t, __) uaction **)

  let read_vect_sequential idx =
    uCompleteSwitch (SequentialSwitch ((Bits_t (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0))))))))))))))))))))))))))))))))), ('t'::('m'::('p'::[])))))
      (Nat.log2_up (add capacity (Pervasives.succ 0))) idx (fun idx0 -> URead
      (P0, (Coq_stack idx0)))

  (** val write0_stack :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let write0_stack =
    { int_name =
      ('w'::('r'::('i'::('t'::('e'::('0'::('_'::('q'::('u'::('e'::('u'::('e'::[]))))))))))));
      int_argspec =
      (app
        ((prod_of_argsig { arg_name = ('i'::('d'::('x'::[]))); arg_type =
           (Bits_t (Nat.log2_up (add capacity (Pervasives.succ 0)))) }) :: [])
        ((prod_of_argsig { arg_name = ('v'::('a'::('l'::[]))); arg_type =
           (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ
           0))))))))))))))))))))))))))))))))) }) :: [])); int_retSig =
      (Bits_t 0); int_body =
      (uCompleteSwitch SequentialSwitchTt
        (Nat.log2_up (add capacity (Pervasives.succ 0)))
        ('i'::('d'::('x'::[]))) (fun idx -> UWrite (P0, (Coq_stack idx),
        (UVar ('v'::('a'::('l'::[]))))))) }

  (** val push :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let push =
    { int_name = ('p'::('u'::('s'::('h'::[])))); int_argspec =
      ((prod_of_argsig { arg_name =
         ('a'::('d'::('d'::('r'::('e'::('s'::('s'::[]))))))); arg_type =
         (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ 0))))))))))))))))))))))))))))))))) }) :: []);
      int_retSig = (Bits_t (Pervasives.succ 0)); int_body = (UBind
      (('s'::('0'::[])), (URead (P0, Coq_size)), (UIf ((UBinop
      ((PrimUntyped.UEq false), (UVar ('s'::('0'::[]))), (USugar (UConstBits
      ((Nat.log2_up (add capacity (Pervasives.succ 0))),
      (Bits.of_nat (Nat.log2_up (add capacity (Pervasives.succ 0))) capacity)))))),
      (USugar (UConstBits ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 true __)))), (USeq ((USeq ((USugar (UCallModule
      ({ finite_index = (fun x ->
      match Obj.magic x with
      | Coq_size -> 0
      | Coq_stack n0 ->
        add (Pervasives.succ 0)
          ((finiteType_index
             (pow2 (Nat.log2_up (add capacity (Pervasives.succ 0))))).finite_index
            n0)); finite_elements =
      ((Obj.magic Coq_size) :: (app
                                 (map (Obj.magic (fun x -> Coq_stack x))
                                   (finiteType_index
                                     (pow2
                                       (Nat.log2_up
                                         (add capacity (Pervasives.succ 0))))).finite_elements)
                                 [])) }, (Obj.magic id), (Obj.magic __),
      (Obj.magic write0_stack),
      (app ((UVar ('s'::('0'::[]))) :: []) ((UVar
        ('a'::('d'::('d'::('r'::('e'::('s'::('s'::[])))))))) :: []))))),
      (UWrite (P0, Coq_size, (UBinop ((PrimUntyped.UBits2 PrimUntyped.UPlus),
      (UVar ('s'::('0'::[]))), (USugar (UConstBits
      ((Nat.log2_up (add capacity (Pervasives.succ 0))),
      (Bits.of_N (Nat.log2_up (add capacity (Pervasives.succ 0))) 1)))))))))),
      (USugar (UConstBits ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 false __)))))))))) }

  (** val pop :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let pop =
    { int_name = ('p'::('o'::('p'::[]))); int_argspec =
      ((prod_of_argsig { arg_name =
         ('a'::('d'::('d'::('r'::('e'::('s'::('s'::[]))))))); arg_type =
         (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ 0))))))))))))))))))))))))))))))))) }) :: []);
      int_retSig = (Bits_t (Pervasives.succ 0)); int_body = (UBind
      (('s'::('0'::[])), (URead (P0, Coq_size)), (UBind
      (('l'::('o'::('c'::[]))), (UBinop ((PrimUntyped.UBits2
      PrimUntyped.UMinus), (UVar ('s'::('0'::[]))), (USugar (UConstBits
      ((Nat.log2_up (add capacity (Pervasives.succ 0))),
      (Bits.of_N (Nat.log2_up (add capacity (Pervasives.succ 0))) 1)))))),
      (UIf ((UBinop ((PrimUntyped.UEq false), (UVar ('s'::('0'::[]))),
      (USugar (UConstBits ((Nat.log2_up (add capacity (Pervasives.succ 0))),
      (Bits.of_N (Nat.log2_up (add capacity (Pervasives.succ 0))) 0)))))),
      (USugar (UConstBits ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 true __)))), (UIf ((UBinop ((PrimUntyped.UEq
      true), (read_vect_sequential ('l'::('o'::('c'::[])))), (UVar
      ('a'::('d'::('d'::('r'::('e'::('s'::('s'::[])))))))))), (USugar
      (UConstBits ((Pervasives.succ 0), (Obj.magic vect_cons 0 true __)))),
      (USeq ((UWrite (P0, Coq_size, (UBinop ((PrimUntyped.UBits2
      PrimUntyped.UMinus), (UVar ('s'::('0'::[]))), (USugar (UConstBits
      ((Nat.log2_up (add capacity (Pervasives.succ 0))),
      (Bits.of_N (Nat.log2_up (add capacity (Pervasives.succ 0))) 1)))))))),
      (USugar (UConstBits ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 false __)))))))))))))) }

  (** val coq_Show_reg_t : reg_t show **)

  let coq_Show_reg_t =
    { show0 = (fun h ->
      match h with
      | Coq_size -> 's'::('i'::('z'::('e'::[])))
      | Coq_stack n0 ->
        's'::('t'::('a'::('c'::('k'::('_'::(Show_nat.string_of_nat
                                             ((fun fthisone fanotherone n -> if n = 0 then fthisone () else fanotherone (n - 1))
                                                (fun _ -> 0)
                                                (fun idx -> Pervasives.succ
                                                ((fun fthisone fanotherone n -> if n = 0 then fthisone () else fanotherone (n - 1))
                                                   (fun _ -> 0)
                                                   (fun idx0 ->
                                                   Pervasives.succ
                                                   ((fun fthisone fanotherone n -> if n = 0 then fthisone () else fanotherone (n - 1))
                                                      (fun _ ->
                                                      0)
                                                      (fun idx1 ->
                                                      Pervasives.succ
                                                      ((fun fthisone fanotherone n -> if n = 0 then fthisone () else fanotherone (n - 1))
                                                         (fun _ ->
                                                         0)
                                                         (fun idx2 ->
                                                         Pervasives.succ
                                                         ((fun fthisone fanotherone n -> if n = 0 then fthisone () else fanotherone (n - 1))
                                                            (fun _ ->
                                                            0)
                                                            (fun idx3 ->
                                                            Pervasives.succ
                                                            ((fun fthisone fanotherone n -> if n = 0 then fthisone () else fanotherone (n - 1))
                                                               (fun _ ->
                                                               0)
                                                               (fun idx4 ->
                                                               Pervasives.succ
                                                               ((fun fthisone fanotherone n -> if n = 0 then fthisone () else fanotherone (n - 1))
                                                                  (fun _ ->
                                                                  0)
                                                                  (fun idx5 ->
                                                                  Pervasives.succ
                                                                  ((fun fthisone fanotherone n -> if n = 0 then fthisone () else fanotherone (n - 1))
                                                                    (fun _ ->
                                                                    0)
                                                                    (fun _ ->
                                                                    Pervasives.succ
                                                                    (assert false
                                                                    (* absurd case *)))
                                                                    idx5))
                                                                  idx4))
                                                               idx3))
                                                            idx2))
                                                         idx1))
                                                      idx0))
                                                   idx))
                                                (Obj.magic n0))))))))) }

  (** val coq_FiniteType_reg_t : reg_t finiteType **)

  let coq_FiniteType_reg_t =
    { finite_index = (fun x ->
      match x with
      | Coq_size -> 0
      | Coq_stack n0 ->
        add (Pervasives.succ 0)
          ((finiteType_index
             (pow2 (Nat.log2_up (add capacity (Pervasives.succ 0))))).finite_index
            n0)); finite_elements =
      (Coq_size :: (app
                     (map (fun x -> Coq_stack x)
                       (finiteType_index
                         (pow2
                           (Nat.log2_up (add capacity (Pervasives.succ 0))))).finite_elements)
                     [])) }
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

(** val get_i_field_name : i_field -> char list **)

let get_i_field_name = function
| Opcode -> 'o'::('p'::('c'::('o'::('d'::('e'::[])))))
| Fct2 -> 'f'::('u'::('n'::('c'::('t'::('2'::[])))))
| Fct3 -> 'f'::('u'::('n'::('c'::('t'::('3'::[])))))
| Fct7 -> 'f'::('u'::('n'::('c'::('t'::('7'::[])))))
| Rs1 -> 'r'::('s'::('1'::[]))
| Rs2 -> 'r'::('s'::('2'::[]))
| Rs3 -> 'r'::('s'::('3'::[]))
| Rd -> 'r'::('d'::[])
| ImmI -> 'i'::('m'::('m'::('I'::[])))
| ImmS -> 'i'::('m'::('m'::('S'::[])))
| ImmB -> 'i'::('m'::('m'::('B'::[])))
| ImmU -> 'i'::('m'::('m'::('U'::[])))
| ImmJ -> 'i'::('m'::('m'::('J'::[])))

(** val has_opcode : i_type -> bool **)

let has_opcode _ =
  true

(** val has_fct2 : i_type -> bool **)

let has_fct2 = function
| R4Type -> true
| _ -> false

(** val has_fct3 : i_type -> bool **)

let has_fct3 = function
| UType -> false
| JType -> false
| _ -> true

(** val has_fct7 : i_type -> bool **)

let has_fct7 = function
| RType -> true
| _ -> false

(** val has_rs1 : i_type -> bool **)

let has_rs1 = function
| UType -> false
| JType -> false
| _ -> true

(** val has_rs2 : i_type -> bool **)

let has_rs2 = function
| IType -> false
| UType -> false
| JType -> false
| _ -> true

(** val has_rs3 : i_type -> bool **)

let has_rs3 = function
| R4Type -> true
| _ -> false

(** val has_rd : i_type -> bool **)

let has_rd = function
| SType -> false
| BType -> false
| _ -> true

(** val has_immI : i_type -> bool **)

let has_immI = function
| IType -> true
| _ -> false

(** val has_immS : i_type -> bool **)

let has_immS = function
| SType -> true
| _ -> false

(** val has_immB : i_type -> bool **)

let has_immB = function
| BType -> true
| _ -> false

(** val has_immU : i_type -> bool **)

let has_immU = function
| UType -> true
| _ -> false

(** val has_immJ : i_type -> bool **)

let has_immJ = function
| JType -> true
| _ -> false

type subfield_properties = { first_bit : int; subfield_length : int }

type i_field_properties = { is_sign_extended : bool; shift : int;
                            i_field_subfields : subfield_properties list }

(** val get_i_field_properties : i_field -> i_field_properties **)

let get_i_field_properties = function
| Opcode ->
  { is_sign_extended = false; shift = 0; i_field_subfields = ({ first_bit =
    0; subfield_length = (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))) } :: []) }
| Fct2 ->
  { is_sign_extended = false; shift = 0; i_field_subfields = ({ first_bit =
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))));
    subfield_length = (Pervasives.succ (Pervasives.succ 0)) } :: []) }
| Fct3 ->
  { is_sign_extended = false; shift = 0; i_field_subfields = ({ first_bit =
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))); subfield_length =
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))) } :: []) }
| Fct7 ->
  { is_sign_extended = false; shift = 0; i_field_subfields = ({ first_bit =
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))));
    subfield_length = (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))) } :: []) }
| Rs1 ->
  { is_sign_extended = false; shift = 0; i_field_subfields = ({ first_bit =
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))); subfield_length =
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))) } :: []) }
| Rs2 ->
  { is_sign_extended = false; shift = 0; i_field_subfields = ({ first_bit =
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))));
    subfield_length = (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))) } :: []) }
| Rs3 ->
  { is_sign_extended = false; shift = 0; i_field_subfields = ({ first_bit =
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))));
    subfield_length = (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))) } :: []) }
| Rd ->
  { is_sign_extended = false; shift = 0; i_field_subfields = ({ first_bit =
    ((fun p->1+2*p) ((fun p->1+2*p) 1)); subfield_length = (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))) } :: []) }
| ImmI ->
  { is_sign_extended = true; shift = 0; i_field_subfields = ({ first_bit =
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))));
    subfield_length = (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))) } :: []) }
| ImmS ->
  { is_sign_extended = true; shift = 0; i_field_subfields = ({ first_bit =
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))));
    subfield_length = (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))) } :: ({ first_bit = ((fun p->1+2*p) ((fun p->1+2*p) 1));
    subfield_length = (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))) } :: [])) }
| ImmB ->
  { is_sign_extended = true; shift = (Pervasives.succ 0); i_field_subfields =
    ({ first_bit = ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) 1)))); subfield_length = (Pervasives.succ
    0) } :: ({ first_bit = ((fun p->1+2*p) ((fun p->1+2*p) 1));
    subfield_length = (Pervasives.succ 0) } :: ({ first_bit = ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))); subfield_length =
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))) } :: ({ first_bit =
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))); subfield_length =
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))) } :: [])))) }
| ImmU ->
  { is_sign_extended = false; shift = (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))))); i_field_subfields =
    ({ first_bit = ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)));
    subfield_length = (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))))))) } :: []) }
| ImmJ ->
  { is_sign_extended = true; shift = (Pervasives.succ 0); i_field_subfields =
    ({ first_bit = ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) 1)))); subfield_length = (Pervasives.succ
    0) } :: ({ first_bit = ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)));
    subfield_length = (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))) } :: ({ first_bit = ((fun p->2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))); subfield_length =
    (Pervasives.succ 0) } :: ({ first_bit = ((fun p->1+2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) 1)))); subfield_length = (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))) } :: [])))) }

(** val rV32I_instructions : instruction list **)

let rV32I_instructions =
  LUI_32I :: (AUIPC_32I :: (JAL_32I :: (JALR_32I :: (BEQ_32I :: (BNE_32I :: (BLT_32I :: (BGE_32I :: (BLTU_32I :: (BGEU_32I :: (LB_32I :: (LH_32I :: (LW_32I :: (LBU_32I :: (LHU_32I :: (SB_32I :: (SH_32I :: (SW_32I :: (ADDI_32I :: (SLTI_32I :: (SLTIU_32I :: (XORI_32I :: (ORI_32I :: (ANDI_32I :: (SLLI_32I :: (SRLI_32I :: (SRAI_32I :: (ADD_32I :: (SUB_32I :: (SLL_32I :: (SLT_32I :: (SLTU_32I :: (XOR_32I :: (SRL_32I :: (SRA_32I :: (OR_32I :: (AND_32I :: (FENCE_32I :: (ECALL_32I :: (EBREAK_32I :: [])))))))))))))))))))))))))))))))))))))))

(** val rV64I_instructions : instruction list **)

let rV64I_instructions =
  LUI_64I :: (AUIPC_64I :: (JAL_64I :: (JALR_64I :: (BEQ_64I :: (BNE_64I :: (BLT_64I :: (BGE_64I :: (BLTU_64I :: (BGEU_64I :: (LB_64I :: (LH_64I :: (LW_64I :: (LBU_64I :: (LHU_64I :: (SB_64I :: (SH_64I :: (SW_64I :: (ADDI_64I :: (SLTI_64I :: (SLTIU_64I :: (XORI_64I :: (ORI_64I :: (ANDI_64I :: (SLLI_64I :: (SRLI_64I :: (SRAI_64I :: (ADD_64I :: (SUB_64I :: (SLL_64I :: (SLT_64I :: (SLTU_64I :: (XOR_64I :: (SRL_64I :: (SRA_64I :: (OR_64I :: (AND_64I :: (FENCE_64I :: (ECALL_64I :: (EBREAK_64I :: (LWU_64I :: (LD_64I :: (SD_64I :: (ADDIW_64I :: (SLLIW_64I :: (SRLIW_64I :: (SRAIW_64I :: (ADDW_64I :: (SUBW_64I :: (SLLW_64I :: (SRLW_64I :: (SRAW_64I :: [])))))))))))))))))))))))))))))))))))))))))))))))))))

(** val rV32Zifencei_instructions : instruction list **)

let rV32Zifencei_instructions =
  FENCE_I_32Zifencei :: []

(** val rV64Zifencei_instructions : instruction list **)

let rV64Zifencei_instructions =
  FENCE_I_64Zifencei :: []

(** val rV32Zicsr_instructions : instruction list **)

let rV32Zicsr_instructions =
  CSRRW_32Zicsr :: (CSRRS_32Zicsr :: (CSRRC_32Zicsr :: (CSRRWI_32Zicsr :: (CSRRSI_32Zicsr :: (CSRRCI_32Zicsr :: [])))))

(** val rV64Zicsr_instructions : instruction list **)

let rV64Zicsr_instructions =
  CSRRW_64Zicsr :: (CSRRS_64Zicsr :: (CSRRC_64Zicsr :: (CSRRWI_64Zicsr :: (CSRRSI_64Zicsr :: (CSRRCI_64Zicsr :: [])))))

(** val rV32M_instructions : instruction list **)

let rV32M_instructions =
  MUL_32M :: (MULH_32M :: (MULHSU_32M :: (MULHU_32M :: (DIV_32M :: (DIVU_32M :: (REM_32M :: (REMU_32M :: [])))))))

(** val rV64M_instructions : instruction list **)

let rV64M_instructions =
  MUL_64M :: (MULH_64M :: (MULHSU_64M :: (MULHU_64M :: (DIV_64M :: (DIVU_64M :: (REM_64M :: (REMU_64M :: (MULW_64M :: (DIVW_64M :: (DIVUW_64M :: (REMW_64M :: (REMUW_64M :: []))))))))))))

(** val rV32A_instructions : instruction list **)

let rV32A_instructions =
  LR_W_00_32A :: (LR_W_01_32A :: (LR_W_10_32A :: (LR_W_11_32A :: (SC_W_00_32A :: (SC_W_01_32A :: (SC_W_10_32A :: (SC_W_11_32A :: (AMOSWAP_W_00_32A :: (AMOSWAP_W_01_32A :: (AMOSWAP_W_10_32A :: (AMOSWAP_W_11_32A :: (AMOADD_W_00_32A :: (AMOADD_W_01_32A :: (AMOADD_W_10_32A :: (AMOADD_W_11_32A :: (AMOXOR_W_00_32A :: (AMOXOR_W_01_32A :: (AMOXOR_W_10_32A :: (AMOXOR_W_11_32A :: (AMOAND_W_00_32A :: (AMOAND_W_01_32A :: (AMOAND_W_10_32A :: (AMOAND_W_11_32A :: (AMOOR_W_00_32A :: (AMOOR_W_01_32A :: (AMOOR_W_10_32A :: (AMOOR_W_11_32A :: (AMOMIN_W_00_32A :: (AMOMIN_W_01_32A :: (AMOMIN_W_10_32A :: (AMOMIN_W_11_32A :: (AMOMAX_W_00_32A :: (AMOMAX_W_01_32A :: (AMOMAX_W_10_32A :: (AMOMAX_W_11_32A :: (AMOMINU_W_00_32A :: (AMOMINU_W_01_32A :: (AMOMINU_W_10_32A :: (AMOMINU_W_11_32A :: (AMOMAXU_W_00_32A :: (AMOMAXU_W_01_32A :: (AMOMAXU_W_10_32A :: (AMOMAXU_W_11_32A :: [])))))))))))))))))))))))))))))))))))))))))))

(** val rV64A_instructions : instruction list **)

let rV64A_instructions =
  LR_W_00_64A :: (LR_W_01_64A :: (LR_W_10_64A :: (LR_W_11_64A :: (SC_W_00_64A :: (SC_W_01_64A :: (SC_W_10_64A :: (SC_W_11_64A :: (AMOSWAP_W_00_64A :: (AMOSWAP_W_01_64A :: (AMOSWAP_W_10_64A :: (AMOSWAP_W_11_64A :: (AMOADD_W_00_64A :: (AMOADD_W_01_64A :: (AMOADD_W_10_64A :: (AMOADD_W_11_64A :: (AMOXOR_W_00_64A :: (AMOXOR_W_01_64A :: (AMOXOR_W_10_64A :: (AMOXOR_W_11_64A :: (AMOAND_W_00_64A :: (AMOAND_W_01_64A :: (AMOAND_W_10_64A :: (AMOAND_W_11_64A :: (AMOOR_W_00_64A :: (AMOOR_W_01_64A :: (AMOOR_W_10_64A :: (AMOOR_W_11_64A :: (AMOMIN_W_00_64A :: (AMOMIN_W_01_64A :: (AMOMIN_W_10_64A :: (AMOMIN_W_11_64A :: (AMOMAX_W_00_64A :: (AMOMAX_W_01_64A :: (AMOMAX_W_10_64A :: (AMOMAX_W_11_64A :: (AMOMINU_W_00_64A :: (AMOMINU_W_01_64A :: (AMOMINU_W_10_64A :: (AMOMINU_W_11_64A :: (AMOMAXU_W_00_64A :: (AMOMAXU_W_01_64A :: (AMOMAXU_W_10_64A :: (AMOMAXU_W_11_64A :: (LR_D_00_64A :: (LR_D_01_64A :: (LR_D_10_64A :: (LR_D_11_64A :: (SC_D_00_64A :: (SC_D_01_64A :: (SC_D_10_64A :: (SC_D_11_64A :: (AMOSWAP_D_00_64A :: (AMOSWAP_D_01_64A :: (AMOSWAP_D_10_64A :: (AMOSWAP_D_11_64A :: (AMOADD_D_00_64A :: (AMOADD_D_01_64A :: (AMOADD_D_10_64A :: (AMOADD_D_11_64A :: (AMOXOR_D_00_64A :: (AMOXOR_D_01_64A :: (AMOXOR_D_10_64A :: (AMOXOR_D_11_64A :: (AMOAND_D_00_64A :: (AMOAND_D_01_64A :: (AMOAND_D_10_64A :: (AMOAND_D_11_64A :: (AMOOR_D_00_64A :: (AMOOR_D_01_64A :: (AMOOR_D_10_64A :: (AMOOR_D_11_64A :: (AMOMIN_D_00_64A :: (AMOMIN_D_01_64A :: (AMOMIN_D_10_64A :: (AMOMIN_D_11_64A :: (AMOMAX_D_00_64A :: (AMOMAX_D_01_64A :: (AMOMAX_D_10_64A :: (AMOMAX_D_11_64A :: (AMOMINU_D_00_64A :: (AMOMINU_D_01_64A :: (AMOMINU_D_10_64A :: (AMOMINU_D_11_64A :: (AMOMAXU_D_00_64A :: (AMOMAXU_D_01_64A :: (AMOMAXU_D_10_64A :: (AMOMAXU_D_11_64A :: [])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val rV32F_instructions : instruction list **)

let rV32F_instructions =
  FLW_32F :: (FSW_32F :: (FMADD_RNE_S_32F :: (FMADD_RTZ_S_32F :: (FMADD_RDN_S_32F :: (FMADD_RUP_S_32F :: (FMADD_RMM_S_32F :: (FMADD_DYN_S_32F :: (FMSUB_RNE_S_32F :: (FMSUB_RTZ_S_32F :: (FMSUB_RDN_S_32F :: (FMSUB_RUP_S_32F :: (FMSUB_RMM_S_32F :: (FMSUB_DYN_S_32F :: (FNMSUB_RNE_S_32F :: (FNMSUB_RTZ_S_32F :: (FNMSUB_RDN_S_32F :: (FNMSUB_RUP_S_32F :: (FNMSUB_RMM_S_32F :: (FNMSUB_DYN_S_32F :: (FNMADD_RNE_S_32F :: (FNMADD_RTZ_S_32F :: (FNMADD_RDN_S_32F :: (FNMADD_RUP_S_32F :: (FNMADD_RMM_S_32F :: (FNMADD_DYN_S_32F :: (FADD_RNE_S_32F :: (FADD_RTZ_S_32F :: (FADD_RDN_S_32F :: (FADD_RUP_S_32F :: (FADD_RMM_S_32F :: (FADD_DYN_S_32F :: (FSUB_RNE_S_32F :: (FSUB_RTZ_S_32F :: (FSUB_RDN_S_32F :: (FSUB_RUP_S_32F :: (FSUB_RMM_S_32F :: (FSUB_DYN_S_32F :: (FMUL_RNE_S_32F :: (FMUL_RTZ_S_32F :: (FMUL_RDN_S_32F :: (FMUL_RUP_S_32F :: (FMUL_RMM_S_32F :: (FMUL_DYN_S_32F :: (FDIV_RNE_S_32F :: (FDIV_RTZ_S_32F :: (FDIV_RDN_S_32F :: (FDIV_RUP_S_32F :: (FDIV_RMM_S_32F :: (FDIV_DYN_S_32F :: (FSQRT_RNE_S_32F :: (FSQRT_RTZ_S_32F :: (FSQRT_RDN_S_32F :: (FSQRT_RUP_S_32F :: (FSQRT_RMM_S_32F :: (FSQRT_DYN_S_32F :: (FSGNJ_S_32F :: (FSGNJN_S_32F :: (FSGNJX_S_32F :: (FMIN_S_32F :: (FMAX_S_32F :: (FCVT_RNE_W_S_32F :: (FCVT_RTZ_W_S_32F :: (FCVT_RDN_W_S_32F :: (FCVT_RUP_W_S_32F :: (FCVT_RMM_W_S_32F :: (FCVT_DYN_W_S_32F :: (FCVT_RNE_WU_S_32F :: (FCVT_RTZ_WU_S_32F :: (FCVT_RDN_WU_S_32F :: (FCVT_RUP_WU_S_32F :: (FCVT_RMM_WU_S_32F :: (FCVT_DYN_WU_S_32F :: (FMV_X_W_32F :: (FEQ_S_32F :: (FLT_S_32F :: (FLE_S_32F :: (FCLASS_S_32F :: (FCVT_RNE_S_W_32F :: (FCVT_RTZ_S_W_32F :: (FCVT_RDN_S_W_32F :: (FCVT_RUP_S_W_32F :: (FCVT_RMM_S_W_32F :: (FCVT_DYN_S_W_32F :: (FCVT_RNE_S_WU_32F :: (FCVT_RTZ_S_WU_32F :: (FCVT_RDN_S_WU_32F :: (FCVT_RUP_S_WU_32F :: (FCVT_RMM_S_WU_32F :: (FCVT_DYN_S_WU_32F :: (FMV_W_X_32F :: []))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val rV64F_instructions : instruction list **)

let rV64F_instructions =
  FLW_64F :: (FSW_64F :: (FMADD_RNE_S_64F :: (FMADD_RTZ_S_64F :: (FMADD_RDN_S_64F :: (FMADD_RUP_S_64F :: (FMADD_RMM_S_64F :: (FMADD_DYN_S_64F :: (FMSUB_RNE_S_64F :: (FMSUB_RTZ_S_64F :: (FMSUB_RDN_S_64F :: (FMSUB_RUP_S_64F :: (FMSUB_RMM_S_64F :: (FMSUB_DYN_S_64F :: (FNMSUB_RNE_S_64F :: (FNMSUB_RTZ_S_64F :: (FNMSUB_RDN_S_64F :: (FNMSUB_RUP_S_64F :: (FNMSUB_RMM_S_64F :: (FNMSUB_DYN_S_64F :: (FNMADD_RNE_S_64F :: (FNMADD_RTZ_S_64F :: (FNMADD_RDN_S_64F :: (FNMADD_RUP_S_64F :: (FNMADD_RMM_S_64F :: (FNMADD_DYN_S_64F :: (FADD_RNE_S_64F :: (FADD_RTZ_S_64F :: (FADD_RDN_S_64F :: (FADD_RUP_S_64F :: (FADD_RMM_S_64F :: (FADD_DYN_S_64F :: (FSUB_RNE_S_64F :: (FSUB_RTZ_S_64F :: (FSUB_RDN_S_64F :: (FSUB_RUP_S_64F :: (FSUB_RMM_S_64F :: (FSUB_DYN_S_64F :: (FMUL_RNE_S_64F :: (FMUL_RTZ_S_64F :: (FMUL_RDN_S_64F :: (FMUL_RUP_S_64F :: (FMUL_RMM_S_64F :: (FMUL_DYN_S_64F :: (FDIV_RNE_S_64F :: (FDIV_RTZ_S_64F :: (FDIV_RDN_S_64F :: (FDIV_RUP_S_64F :: (FDIV_RMM_S_64F :: (FDIV_DYN_S_64F :: (FSQRT_RNE_S_64F :: (FSQRT_RTZ_S_64F :: (FSQRT_RDN_S_64F :: (FSQRT_RUP_S_64F :: (FSQRT_RMM_S_64F :: (FSQRT_DYN_S_64F :: (FSGNJ_S_64F :: (FSGNJN_S_64F :: (FSGNJX_S_64F :: (FMIN_S_64F :: (FMAX_S_64F :: (FCVT_RNE_W_S_64F :: (FCVT_RTZ_W_S_64F :: (FCVT_RDN_W_S_64F :: (FCVT_RUP_W_S_64F :: (FCVT_RMM_W_S_64F :: (FCVT_DYN_W_S_64F :: (FCVT_RNE_WU_S_64F :: (FCVT_RTZ_WU_S_64F :: (FCVT_RDN_WU_S_64F :: (FCVT_RUP_WU_S_64F :: (FCVT_RMM_WU_S_64F :: (FCVT_DYN_WU_S_64F :: (FMV_X_W_64F :: (FEQ_S_64F :: (FLT_S_64F :: (FLE_S_64F :: (FCLASS_S_64F :: (FCVT_RNE_S_W_64F :: (FCVT_RTZ_S_W_64F :: (FCVT_RDN_S_W_64F :: (FCVT_RUP_S_W_64F :: (FCVT_RMM_S_W_64F :: (FCVT_DYN_S_W_64F :: (FCVT_RNE_S_WU_64F :: (FCVT_RTZ_S_WU_64F :: (FCVT_RDN_S_WU_64F :: (FCVT_RUP_S_WU_64F :: (FCVT_RMM_S_WU_64F :: (FCVT_DYN_S_WU_64F :: (FMV_W_X_64F :: (FCVT_RNE_L_S_64F :: (FCVT_RTZ_L_S_64F :: (FCVT_RDN_L_S_64F :: (FCVT_RUP_L_S_64F :: (FCVT_RMM_L_S_64F :: (FCVT_DYN_L_S_64F :: (FCVT_RNE_LU_S_64F :: (FCVT_RTZ_LU_S_64F :: (FCVT_RDN_LU_S_64F :: (FCVT_RUP_LU_S_64F :: (FCVT_RMM_LU_S_64F :: (FCVT_DYN_LU_S_64F :: (FCVT_RNE_S_L_64F :: (FCVT_RTZ_S_L_64F :: (FCVT_RDN_S_L_64F :: (FCVT_RUP_S_L_64F :: (FCVT_RMM_S_L_64F :: (FCVT_DYN_S_L_64F :: (FCVT_RNE_S_LU_64F :: (FCVT_RTZ_S_LU_64F :: (FCVT_RDN_S_LU_64F :: (FCVT_RUP_S_LU_64F :: (FCVT_RMM_S_LU_64F :: (FCVT_DYN_S_LU_64F :: []))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val rV32D_instructions : instruction list **)

let rV32D_instructions =
  FLD_32D :: (FSD_32D :: (FMADD_RNE_D_32D :: (FMADD_RTZ_D_32D :: (FMADD_RDN_D_32D :: (FMADD_RUP_D_32D :: (FMADD_RMM_D_32D :: (FMADD_DYN_D_32D :: (FMSUB_RNE_D_32D :: (FMSUB_RTZ_D_32D :: (FMSUB_RDN_D_32D :: (FMSUB_RUP_D_32D :: (FMSUB_RMM_D_32D :: (FMSUB_DYN_D_32D :: (FNMSUB_RNE_D_32D :: (FNMSUB_RTZ_D_32D :: (FNMSUB_RDN_D_32D :: (FNMSUB_RUP_D_32D :: (FNMSUB_RMM_D_32D :: (FNMSUB_DYN_D_32D :: (FNMADD_RNE_D_32D :: (FNMADD_RTZ_D_32D :: (FNMADD_RDN_D_32D :: (FNMADD_RUP_D_32D :: (FNMADD_RMM_D_32D :: (FNMADD_DYN_D_32D :: (FADD_RNE_D_32D :: (FADD_RTZ_D_32D :: (FADD_RDN_D_32D :: (FADD_RUP_D_32D :: (FADD_RMM_D_32D :: (FADD_DYN_D_32D :: (FSUB_RNE_D_32D :: (FSUB_RTZ_D_32D :: (FSUB_RDN_D_32D :: (FSUB_RUP_D_32D :: (FSUB_RMM_D_32D :: (FSUB_DYN_D_32D :: (FMUL_RNE_D_32D :: (FMUL_RTZ_D_32D :: (FMUL_RDN_D_32D :: (FMUL_RUP_D_32D :: (FMUL_RMM_D_32D :: (FMUL_DYN_D_32D :: (FDIV_RNE_D_32D :: (FDIV_RTZ_D_32D :: (FDIV_RDN_D_32D :: (FDIV_RUP_D_32D :: (FDIV_RMM_D_32D :: (FDIV_DYN_D_32D :: (FSQRT_RNE_D_32D :: (FSQRT_RTZ_D_32D :: (FSQRT_RDN_D_32D :: (FSQRT_RUP_D_32D :: (FSQRT_RMM_D_32D :: (FSQRT_DYN_D_32D :: (FSGNJ_D_32D :: (FSGNJN_D_32D :: (FSGNJX_D_32D :: (FMIN_D_32D :: (FMAX_D_32D :: (FCVT_RNE_S_D_32D :: (FCVT_RTZ_S_D_32D :: (FCVT_RDN_S_D_32D :: (FCVT_RUP_S_D_32D :: (FCVT_RMM_S_D_32D :: (FCVT_DYN_S_D_32D :: (FCVT_RNE_D_S_32D :: (FCVT_RTZ_D_S_32D :: (FCVT_RDN_D_S_32D :: (FCVT_RUP_D_S_32D :: (FCVT_RMM_D_S_32D :: (FCVT_DYN_D_S_32D :: (FEQ_D_32D :: (FLT_D_32D :: (FLE_D_32D :: (FCLASS_D_32D :: (FCVT_RNE_W_D_32D :: (FCVT_RTZ_W_D_32D :: (FCVT_RDN_W_D_32D :: (FCVT_RUP_W_D_32D :: (FCVT_RMM_W_D_32D :: (FCVT_DYN_W_D_32D :: (FCVT_RNE_WU_D_32D :: (FCVT_RTZ_WU_D_32D :: (FCVT_RDN_WU_D_32D :: (FCVT_RUP_WU_D_32D :: (FCVT_RMM_WU_D_32D :: (FCVT_DYN_WU_D_32D :: (FCVT_RNE_D_W_32D :: (FCVT_RTZ_D_W_32D :: (FCVT_RDN_D_W_32D :: (FCVT_RUP_D_W_32D :: (FCVT_RMM_D_W_32D :: (FCVT_DYN_D_W_32D :: (FCVT_RNE_D_WU_32D :: (FCVT_RTZ_D_WU_32D :: (FCVT_RDN_D_WU_32D :: (FCVT_RUP_D_WU_32D :: (FCVT_RMM_D_WU_32D :: (FCVT_DYN_D_WU_32D :: []))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val rV64D_instructions : instruction list **)

let rV64D_instructions =
  FLD_64D :: (FSD_64D :: (FMADD_RNE_D_64D :: (FMADD_RTZ_D_64D :: (FMADD_RDN_D_64D :: (FMADD_RUP_D_64D :: (FMADD_RMM_D_64D :: (FMADD_DYN_D_64D :: (FMSUB_RNE_D_64D :: (FMSUB_RTZ_D_64D :: (FMSUB_RDN_D_64D :: (FMSUB_RUP_D_64D :: (FMSUB_RMM_D_64D :: (FMSUB_DYN_D_64D :: (FNMSUB_RNE_D_64D :: (FNMSUB_RTZ_D_64D :: (FNMSUB_RDN_D_64D :: (FNMSUB_RUP_D_64D :: (FNMSUB_RMM_D_64D :: (FNMSUB_DYN_D_64D :: (FNMADD_RNE_D_64D :: (FNMADD_RTZ_D_64D :: (FNMADD_RDN_D_64D :: (FNMADD_RUP_D_64D :: (FNMADD_RMM_D_64D :: (FNMADD_DYN_D_64D :: (FADD_RNE_D_64D :: (FADD_RTZ_D_64D :: (FADD_RDN_D_64D :: (FADD_RUP_D_64D :: (FADD_RMM_D_64D :: (FADD_DYN_D_64D :: (FSUB_RNE_D_64D :: (FSUB_RTZ_D_64D :: (FSUB_RDN_D_64D :: (FSUB_RUP_D_64D :: (FSUB_RMM_D_64D :: (FSUB_DYN_D_64D :: (FMUL_RNE_D_64D :: (FMUL_RTZ_D_64D :: (FMUL_RDN_D_64D :: (FMUL_RUP_D_64D :: (FMUL_RMM_D_64D :: (FMUL_DYN_D_64D :: (FDIV_RNE_D_64D :: (FDIV_RTZ_D_64D :: (FDIV_RDN_D_64D :: (FDIV_RUP_D_64D :: (FDIV_RMM_D_64D :: (FDIV_DYN_D_64D :: (FSQRT_RNE_D_64D :: (FSQRT_RTZ_D_64D :: (FSQRT_RDN_D_64D :: (FSQRT_RUP_D_64D :: (FSQRT_RMM_D_64D :: (FSQRT_DYN_D_64D :: (FSGNJ_D_64D :: (FSGNJN_D_64D :: (FSGNJX_D_64D :: (FMIN_D_64D :: (FMAX_D_64D :: (FCVT_RNE_S_D_64D :: (FCVT_RTZ_S_D_64D :: (FCVT_RDN_S_D_64D :: (FCVT_RUP_S_D_64D :: (FCVT_RMM_S_D_64D :: (FCVT_DYN_S_D_64D :: (FCVT_RNE_D_S_64D :: (FCVT_RTZ_D_S_64D :: (FCVT_RDN_D_S_64D :: (FCVT_RUP_D_S_64D :: (FCVT_RMM_D_S_64D :: (FCVT_DYN_D_S_64D :: (FEQ_D_64D :: (FLT_D_64D :: (FLE_D_64D :: (FCLASS_D_64D :: (FCVT_RNE_W_D_64D :: (FCVT_RTZ_W_D_64D :: (FCVT_RDN_W_D_64D :: (FCVT_RUP_W_D_64D :: (FCVT_RMM_W_D_64D :: (FCVT_DYN_W_D_64D :: (FCVT_RNE_WU_D_64D :: (FCVT_RTZ_WU_D_64D :: (FCVT_RDN_WU_D_64D :: (FCVT_RUP_WU_D_64D :: (FCVT_RMM_WU_D_64D :: (FCVT_DYN_WU_D_64D :: (FCVT_RNE_D_W_64D :: (FCVT_RTZ_D_W_64D :: (FCVT_RDN_D_W_64D :: (FCVT_RUP_D_W_64D :: (FCVT_RMM_D_W_64D :: (FCVT_DYN_D_W_64D :: (FCVT_RNE_D_WU_64D :: (FCVT_RTZ_D_WU_64D :: (FCVT_RDN_D_WU_64D :: (FCVT_RUP_D_WU_64D :: (FCVT_RMM_D_WU_64D :: (FCVT_DYN_D_WU_64D :: (FCVT_RNE_L_D_64D :: (FCVT_RTZ_L_D_64D :: (FCVT_RDN_L_D_64D :: (FCVT_RUP_L_D_64D :: (FCVT_RMM_L_D_64D :: (FCVT_DYN_L_D_64D :: (FCVT_RNE_LU_D_64D :: (FCVT_RTZ_LU_D_64D :: (FCVT_RDN_LU_D_64D :: (FCVT_RUP_LU_D_64D :: (FCVT_RMM_LU_D_64D :: (FCVT_DYN_LU_D_64D :: (FMV_X_D_64D :: (FCVT_RNE_D_L_64D :: (FCVT_RTZ_D_L_64D :: (FCVT_RDN_D_L_64D :: (FCVT_RUP_D_L_64D :: (FCVT_RMM_D_L_64D :: (FCVT_DYN_D_L_64D :: (FCVT_RNE_D_LU_64D :: (FCVT_RTZ_D_LU_64D :: (FCVT_RDN_D_LU_64D :: (FCVT_RUP_D_LU_64D :: (FCVT_RMM_D_LU_64D :: (FCVT_DYN_D_LU_64D :: (FMV_D_X_64D :: []))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val rV32Q_instructions : instruction list **)

let rV32Q_instructions =
  FLQ_32Q :: (FSQ_32Q :: (FMADD_RNE_Q_32Q :: (FMADD_RTZ_Q_32Q :: (FMADD_RDN_Q_32Q :: (FMADD_RUP_Q_32Q :: (FMADD_RMM_Q_32Q :: (FMADD_DYN_Q_32Q :: (FMSUB_RNE_Q_32Q :: (FMSUB_RTZ_Q_32Q :: (FMSUB_RDN_Q_32Q :: (FMSUB_RUP_Q_32Q :: (FMSUB_RMM_Q_32Q :: (FMSUB_DYN_Q_32Q :: (FNMSUB_RNE_Q_32Q :: (FNMSUB_RTZ_Q_32Q :: (FNMSUB_RDN_Q_32Q :: (FNMSUB_RUP_Q_32Q :: (FNMSUB_RMM_Q_32Q :: (FNMSUB_DYN_Q_32Q :: (FNMADD_RNE_Q_32Q :: (FNMADD_RTZ_Q_32Q :: (FNMADD_RDN_Q_32Q :: (FNMADD_RUP_Q_32Q :: (FNMADD_RMM_Q_32Q :: (FNMADD_DYN_Q_32Q :: (FADD_RNE_Q_32Q :: (FADD_RTZ_Q_32Q :: (FADD_RDN_Q_32Q :: (FADD_RUP_Q_32Q :: (FADD_RMM_Q_32Q :: (FADD_DYN_Q_32Q :: (FSUB_RNE_Q_32Q :: (FSUB_RTZ_Q_32Q :: (FSUB_RDN_Q_32Q :: (FSUB_RUP_Q_32Q :: (FSUB_RMM_Q_32Q :: (FSUB_DYN_Q_32Q :: (FMUL_RNE_Q_32Q :: (FMUL_RTZ_Q_32Q :: (FMUL_RDN_Q_32Q :: (FMUL_RUP_Q_32Q :: (FMUL_RMM_Q_32Q :: (FMUL_DYN_Q_32Q :: (FDIV_RNE_Q_32Q :: (FDIV_RTZ_Q_32Q :: (FDIV_RDN_Q_32Q :: (FDIV_RUP_Q_32Q :: (FDIV_RMM_Q_32Q :: (FDIV_DYN_Q_32Q :: (FSQRT_RNE_Q_32Q :: (FSQRT_RTZ_Q_32Q :: (FSQRT_RDN_Q_32Q :: (FSQRT_RUP_Q_32Q :: (FSQRT_RMM_Q_32Q :: (FSQRT_DYN_Q_32Q :: (FSGNJ_Q_32Q :: (FSGNJN_Q_32Q :: (FSGNJX_Q_32Q :: (FMIN_Q_32Q :: (FMAX_Q_32Q :: (FCVT_RNE_S_Q_32Q :: (FCVT_RTZ_S_Q_32Q :: (FCVT_RDN_S_Q_32Q :: (FCVT_RUP_S_Q_32Q :: (FCVT_RMM_S_Q_32Q :: (FCVT_DYN_S_Q_32Q :: (FCVT_RNE_Q_S_32Q :: (FCVT_RTZ_Q_S_32Q :: (FCVT_RDN_Q_S_32Q :: (FCVT_RUP_Q_S_32Q :: (FCVT_RMM_Q_S_32Q :: (FCVT_DYN_Q_S_32Q :: (FCVT_RNE_D_Q_32Q :: (FCVT_RTZ_D_Q_32Q :: (FCVT_RDN_D_Q_32Q :: (FCVT_RUP_D_Q_32Q :: (FCVT_RMM_D_Q_32Q :: (FCVT_DYN_D_Q_32Q :: (FCVT_RNE_Q_D_32Q :: (FCVT_RTZ_Q_D_32Q :: (FCVT_RDN_Q_D_32Q :: (FCVT_RUP_Q_D_32Q :: (FCVT_RMM_Q_D_32Q :: (FCVT_DYN_Q_D_32Q :: (FEQ_Q_32Q :: (FLT_Q_32Q :: (FLE_Q_32Q :: (FCLASS_Q_32Q :: (FCVT_RNE_W_Q_32Q :: (FCVT_RTZ_W_Q_32Q :: (FCVT_RDN_W_Q_32Q :: (FCVT_RUP_W_Q_32Q :: (FCVT_RMM_W_Q_32Q :: (FCVT_DYN_W_Q_32Q :: (FCVT_RNE_WU_Q_32Q :: (FCVT_RTZ_WU_Q_32Q :: (FCVT_RDN_WU_Q_32Q :: (FCVT_RUP_WU_Q_32Q :: (FCVT_RMM_WU_Q_32Q :: (FCVT_DYN_WU_Q_32Q :: (FCVT_RNE_Q_W_32Q :: (FCVT_RTZ_Q_W_32Q :: (FCVT_RDN_Q_W_32Q :: (FCVT_RUP_Q_W_32Q :: (FCVT_RMM_Q_W_32Q :: (FCVT_DYN_Q_W_32Q :: (FCVT_RNE_Q_WU_32Q :: (FCVT_RTZ_Q_WU_32Q :: (FCVT_RDN_Q_WU_32Q :: (FCVT_RUP_Q_WU_32Q :: (FCVT_RMM_Q_WU_32Q :: (FCVT_DYN_Q_WU_32Q :: []))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val rV64Q_instructions : instruction list **)

let rV64Q_instructions =
  FLQ_64Q :: (FSQ_64Q :: (FMADD_RNE_Q_64Q :: (FMADD_RTZ_Q_64Q :: (FMADD_RDN_Q_64Q :: (FMADD_RUP_Q_64Q :: (FMADD_RMM_Q_64Q :: (FMADD_DYN_Q_64Q :: (FMSUB_RNE_Q_64Q :: (FMSUB_RTZ_Q_64Q :: (FMSUB_RDN_Q_64Q :: (FMSUB_RUP_Q_64Q :: (FMSUB_RMM_Q_64Q :: (FMSUB_DYN_Q_64Q :: (FNMSUB_RNE_Q_64Q :: (FNMSUB_RTZ_Q_64Q :: (FNMSUB_RDN_Q_64Q :: (FNMSUB_RUP_Q_64Q :: (FNMSUB_RMM_Q_64Q :: (FNMSUB_DYN_Q_64Q :: (FNMADD_RNE_Q_64Q :: (FNMADD_RTZ_Q_64Q :: (FNMADD_RDN_Q_64Q :: (FNMADD_RUP_Q_64Q :: (FNMADD_RMM_Q_64Q :: (FNMADD_DYN_Q_64Q :: (FADD_RNE_Q_64Q :: (FADD_RTZ_Q_64Q :: (FADD_RDN_Q_64Q :: (FADD_RUP_Q_64Q :: (FADD_RMM_Q_64Q :: (FADD_DYN_Q_64Q :: (FSUB_RNE_Q_64Q :: (FSUB_RTZ_Q_64Q :: (FSUB_RDN_Q_64Q :: (FSUB_RUP_Q_64Q :: (FSUB_RMM_Q_64Q :: (FSUB_DYN_Q_64Q :: (FMUL_RNE_Q_64Q :: (FMUL_RTZ_Q_64Q :: (FMUL_RDN_Q_64Q :: (FMUL_RUP_Q_64Q :: (FMUL_RMM_Q_64Q :: (FMUL_DYN_Q_64Q :: (FDIV_RNE_Q_64Q :: (FDIV_RTZ_Q_64Q :: (FDIV_RDN_Q_64Q :: (FDIV_RUP_Q_64Q :: (FDIV_RMM_Q_64Q :: (FDIV_DYN_Q_64Q :: (FSQRT_RNE_Q_64Q :: (FSQRT_RTZ_Q_64Q :: (FSQRT_RDN_Q_64Q :: (FSQRT_RUP_Q_64Q :: (FSQRT_RMM_Q_64Q :: (FSQRT_DYN_Q_64Q :: (FSGNJ_Q_64Q :: (FSGNJN_Q_64Q :: (FSGNJX_Q_64Q :: (FMIN_Q_64Q :: (FMAX_Q_64Q :: (FCVT_RNE_S_Q_64Q :: (FCVT_RTZ_S_Q_64Q :: (FCVT_RDN_S_Q_64Q :: (FCVT_RUP_S_Q_64Q :: (FCVT_RMM_S_Q_64Q :: (FCVT_DYN_S_Q_64Q :: (FCVT_RNE_Q_S_64Q :: (FCVT_RTZ_Q_S_64Q :: (FCVT_RDN_Q_S_64Q :: (FCVT_RUP_Q_S_64Q :: (FCVT_RMM_Q_S_64Q :: (FCVT_DYN_Q_S_64Q :: (FCVT_RNE_D_Q_64Q :: (FCVT_RTZ_D_Q_64Q :: (FCVT_RDN_D_Q_64Q :: (FCVT_RUP_D_Q_64Q :: (FCVT_RMM_D_Q_64Q :: (FCVT_DYN_D_Q_64Q :: (FCVT_RNE_Q_D_64Q :: (FCVT_RTZ_Q_D_64Q :: (FCVT_RDN_Q_D_64Q :: (FCVT_RUP_Q_D_64Q :: (FCVT_RMM_Q_D_64Q :: (FCVT_DYN_Q_D_64Q :: (FEQ_Q_64Q :: (FLT_Q_64Q :: (FLE_Q_64Q :: (FCLASS_Q_64Q :: (FCVT_RNE_W_Q_64Q :: (FCVT_RTZ_W_Q_64Q :: (FCVT_RDN_W_Q_64Q :: (FCVT_RUP_W_Q_64Q :: (FCVT_RMM_W_Q_64Q :: (FCVT_DYN_W_Q_64Q :: (FCVT_RNE_WU_Q_64Q :: (FCVT_RTZ_WU_Q_64Q :: (FCVT_RDN_WU_Q_64Q :: (FCVT_RUP_WU_Q_64Q :: (FCVT_RMM_WU_Q_64Q :: (FCVT_DYN_WU_Q_64Q :: (FCVT_RNE_Q_W_64Q :: (FCVT_RTZ_Q_W_64Q :: (FCVT_RDN_Q_W_64Q :: (FCVT_RUP_Q_W_64Q :: (FCVT_RMM_Q_W_64Q :: (FCVT_DYN_Q_W_64Q :: (FCVT_RNE_Q_WU_64Q :: (FCVT_RTZ_Q_WU_64Q :: (FCVT_RDN_Q_WU_64Q :: (FCVT_RUP_Q_WU_64Q :: (FCVT_RMM_Q_WU_64Q :: (FCVT_DYN_Q_WU_64Q :: (FCVT_RNE_L_Q_64Q :: (FCVT_RTZ_L_Q_64Q :: (FCVT_RDN_L_Q_64Q :: (FCVT_RUP_L_Q_64Q :: (FCVT_RMM_L_Q_64Q :: (FCVT_DYN_L_Q_64Q :: (FCVT_RNE_LU_Q_64Q :: (FCVT_RTZ_LU_Q_64Q :: (FCVT_RDN_LU_Q_64Q :: (FCVT_RUP_LU_Q_64Q :: (FCVT_RMM_LU_Q_64Q :: (FCVT_DYN_LU_Q_64Q :: (FCVT_RNE_Q_L_64Q :: (FCVT_RTZ_Q_L_64Q :: (FCVT_RDN_Q_L_64Q :: (FCVT_RUP_Q_L_64Q :: (FCVT_RMM_Q_L_64Q :: (FCVT_DYN_Q_L_64Q :: (FCVT_RNE_Q_LU_64Q :: (FCVT_RTZ_Q_LU_64Q :: (FCVT_RDN_Q_LU_64Q :: (FCVT_RUP_Q_LU_64Q :: (FCVT_RMM_Q_LU_64Q :: (FCVT_DYN_Q_LU_64Q :: []))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val extension_instructions :
    base_standard -> extension -> instruction list **)

let extension_instructions b e =
  match b with
  | RV32I ->
    (match e with
     | RVM -> rV32M_instructions
     | RVA -> rV32A_instructions
     | RVF -> rV32F_instructions
     | RVD -> rV32D_instructions
     | RVQ -> rV32Q_instructions
     | RVZiCSR -> rV32Zicsr_instructions
     | RVZifencei -> rV32Zifencei_instructions)
  | RV64I ->
    (match e with
     | RVM -> rV64M_instructions
     | RVA -> rV64A_instructions
     | RVF -> rV64F_instructions
     | RVD -> rV64D_instructions
     | RVQ -> rV64Q_instructions
     | RVZiCSR -> rV64Zicsr_instructions
     | RVZifencei -> rV64Zifencei_instructions)

(** val iSA_instructions_set : iSA -> instruction list **)

let iSA_instructions_set isa0 =
  app
    (match isa0.iSA_base_standard with
     | RV32I -> rV32I_instructions
     | RV64I -> rV64I_instructions)
    (fold_left (fun i e ->
      app i (extension_instructions isa0.iSA_base_standard e))
      isa0.iSA_extensions [])

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

(** val opcode_name_beq : opcode_name -> opcode_name -> bool **)

let rec opcode_name_beq x y =
  match x with
  | Opc_OP -> (match y with
               | Opc_OP -> true
               | _ -> false)
  | Opc_JALR -> (match y with
                 | Opc_JALR -> true
                 | _ -> false)
  | Opc_LOAD -> (match y with
                 | Opc_LOAD -> true
                 | _ -> false)
  | Opc_OP_IMM -> (match y with
                   | Opc_OP_IMM -> true
                   | _ -> false)
  | Opc_MISC_MEM -> (match y with
                     | Opc_MISC_MEM -> true
                     | _ -> false)
  | Opc_STORE -> (match y with
                  | Opc_STORE -> true
                  | _ -> false)
  | Opc_BRANCH -> (match y with
                   | Opc_BRANCH -> true
                   | _ -> false)
  | Opc_LUI -> (match y with
                | Opc_LUI -> true
                | _ -> false)
  | Opc_AUIPC -> (match y with
                  | Opc_AUIPC -> true
                  | _ -> false)
  | Opc_JAL -> (match y with
                | Opc_JAL -> true
                | _ -> false)
  | Opc_SYSTEM -> (match y with
                   | Opc_SYSTEM -> true
                   | _ -> false)
  | Opc_OP_32 -> (match y with
                  | Opc_OP_32 -> true
                  | _ -> false)
  | Opc_OP_IMM_32 -> (match y with
                      | Opc_OP_IMM_32 -> true
                      | _ -> false)
  | Opc_AMO -> (match y with
                | Opc_AMO -> true
                | _ -> false)
  | Opc_OP_FP -> (match y with
                  | Opc_OP_FP -> true
                  | _ -> false)
  | Opc_MADD -> (match y with
                 | Opc_MADD -> true
                 | _ -> false)
  | Opc_MSUB -> (match y with
                 | Opc_MSUB -> true
                 | _ -> false)
  | Opc_NMSUB -> (match y with
                  | Opc_NMSUB -> true
                  | _ -> false)
  | Opc_NMADD -> (match y with
                  | Opc_NMADD -> true
                  | _ -> false)
  | Opc_LOAD_FP -> (match y with
                    | Opc_LOAD_FP -> true
                    | _ -> false)
  | Opc_STORE_FP -> (match y with
                     | Opc_STORE_FP -> true
                     | _ -> false)

(** val opcode_bin :
    opcode_name -> (bool, (bool, (bool, (bool, (bool, (bool, (bool, __)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t **)

let opcode_bin = function
| Opc_OP ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 false __))))))
| Opc_JALR ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 true __))))))
| Opc_LOAD ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Opc_OP_IMM ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Opc_MISC_MEM ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Opc_STORE ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 false __))))))
| Opc_BRANCH ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 true __))))))
| Opc_LUI ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 false __))))))
| Opc_AUIPC ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Opc_JAL ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 true __))))))
| Opc_SYSTEM ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 true __))))))
| Opc_OP_32 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 false __))))))
| Opc_OP_IMM_32 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Opc_AMO ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 false __))))))
| Opc_OP_FP ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 true __))))))
| Opc_MADD ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 true __))))))
| Opc_MSUB ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 true __))))))
| Opc_NMSUB ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 true __))))))
| Opc_NMADD ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 true __))))))
| Opc_LOAD_FP ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Opc_STORE_FP ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 false __))))))

(** val instruction_opcode : instruction -> opcode_name **)

let instruction_opcode = function
| LUI_32I -> Opc_LUI
| AUIPC_32I -> Opc_AUIPC
| JAL_32I -> Opc_JAL
| JALR_32I -> Opc_JALR
| BEQ_32I -> Opc_BRANCH
| BNE_32I -> Opc_BRANCH
| BLT_32I -> Opc_BRANCH
| BGE_32I -> Opc_BRANCH
| BLTU_32I -> Opc_BRANCH
| BGEU_32I -> Opc_BRANCH
| LB_32I -> Opc_LOAD
| LH_32I -> Opc_LOAD
| LW_32I -> Opc_LOAD
| LBU_32I -> Opc_LOAD
| LHU_32I -> Opc_LOAD
| SB_32I -> Opc_STORE
| SH_32I -> Opc_STORE
| SW_32I -> Opc_STORE
| ADDI_32I -> Opc_OP_IMM
| SLTI_32I -> Opc_OP_IMM
| SLTIU_32I -> Opc_OP_IMM
| XORI_32I -> Opc_OP_IMM
| ORI_32I -> Opc_OP_IMM
| ANDI_32I -> Opc_OP_IMM
| SLLI_32I -> Opc_OP_IMM
| SRLI_32I -> Opc_OP_IMM
| SRAI_32I -> Opc_OP_IMM
| ADD_32I -> Opc_OP
| SUB_32I -> Opc_OP
| SLL_32I -> Opc_OP
| SLT_32I -> Opc_OP
| SLTU_32I -> Opc_OP
| XOR_32I -> Opc_OP
| SRL_32I -> Opc_OP
| SRA_32I -> Opc_OP
| OR_32I -> Opc_OP
| AND_32I -> Opc_OP
| FENCE_32I -> Opc_MISC_MEM
| ECALL_32I -> Opc_SYSTEM
| EBREAK_32I -> Opc_SYSTEM
| LUI_64I -> Opc_LUI
| AUIPC_64I -> Opc_AUIPC
| JAL_64I -> Opc_JAL
| JALR_64I -> Opc_JALR
| BEQ_64I -> Opc_BRANCH
| BNE_64I -> Opc_BRANCH
| BLT_64I -> Opc_BRANCH
| BGE_64I -> Opc_BRANCH
| BLTU_64I -> Opc_BRANCH
| BGEU_64I -> Opc_BRANCH
| LB_64I -> Opc_LOAD
| LH_64I -> Opc_LOAD
| LW_64I -> Opc_LOAD
| LBU_64I -> Opc_LOAD
| LHU_64I -> Opc_LOAD
| SB_64I -> Opc_STORE
| SH_64I -> Opc_STORE
| SW_64I -> Opc_STORE
| ADDI_64I -> Opc_OP_IMM
| SLTI_64I -> Opc_OP_IMM
| SLTIU_64I -> Opc_OP_IMM
| XORI_64I -> Opc_OP_IMM
| ORI_64I -> Opc_OP_IMM
| ANDI_64I -> Opc_OP_IMM
| SLLI_64I -> Opc_OP_IMM
| SRLI_64I -> Opc_OP_IMM
| SRAI_64I -> Opc_OP_IMM
| ADD_64I -> Opc_OP
| SUB_64I -> Opc_OP
| SLL_64I -> Opc_OP
| SLT_64I -> Opc_OP
| SLTU_64I -> Opc_OP
| XOR_64I -> Opc_OP
| SRL_64I -> Opc_OP
| SRA_64I -> Opc_OP
| OR_64I -> Opc_OP
| AND_64I -> Opc_OP
| FENCE_64I -> Opc_MISC_MEM
| ECALL_64I -> Opc_SYSTEM
| EBREAK_64I -> Opc_SYSTEM
| LWU_64I -> Opc_LOAD
| LD_64I -> Opc_LOAD
| SD_64I -> Opc_STORE
| ADDIW_64I -> Opc_OP_IMM_32
| SLLIW_64I -> Opc_OP_IMM_32
| SRLIW_64I -> Opc_OP_IMM_32
| SRAIW_64I -> Opc_OP_IMM_32
| ADDW_64I -> Opc_OP_32
| SUBW_64I -> Opc_OP_32
| SLLW_64I -> Opc_OP_32
| SRLW_64I -> Opc_OP_32
| SRAW_64I -> Opc_OP_32
| FENCE_I_32Zifencei -> Opc_MISC_MEM
| FENCE_I_64Zifencei -> Opc_MISC_MEM
| CSRRW_32Zicsr -> Opc_SYSTEM
| CSRRS_32Zicsr -> Opc_SYSTEM
| CSRRC_32Zicsr -> Opc_SYSTEM
| CSRRWI_32Zicsr -> Opc_SYSTEM
| CSRRSI_32Zicsr -> Opc_SYSTEM
| CSRRCI_32Zicsr -> Opc_SYSTEM
| CSRRW_64Zicsr -> Opc_SYSTEM
| CSRRS_64Zicsr -> Opc_SYSTEM
| CSRRC_64Zicsr -> Opc_SYSTEM
| CSRRWI_64Zicsr -> Opc_SYSTEM
| CSRRSI_64Zicsr -> Opc_SYSTEM
| CSRRCI_64Zicsr -> Opc_SYSTEM
| MUL_32M -> Opc_OP
| MULH_32M -> Opc_OP
| MULHSU_32M -> Opc_OP
| MULHU_32M -> Opc_OP
| DIV_32M -> Opc_OP
| DIVU_32M -> Opc_OP
| REM_32M -> Opc_OP
| REMU_32M -> Opc_OP
| MUL_64M -> Opc_OP
| MULH_64M -> Opc_OP
| MULHSU_64M -> Opc_OP
| MULHU_64M -> Opc_OP
| DIV_64M -> Opc_OP
| DIVU_64M -> Opc_OP
| REM_64M -> Opc_OP
| REMU_64M -> Opc_OP
| MULW_64M -> Opc_OP_32
| DIVW_64M -> Opc_OP_32
| DIVUW_64M -> Opc_OP_32
| REMW_64M -> Opc_OP_32
| REMUW_64M -> Opc_OP_32
| LR_W_00_32A -> Opc_AMO
| LR_W_01_32A -> Opc_AMO
| LR_W_10_32A -> Opc_AMO
| LR_W_11_32A -> Opc_AMO
| SC_W_00_32A -> Opc_AMO
| SC_W_01_32A -> Opc_AMO
| SC_W_10_32A -> Opc_AMO
| SC_W_11_32A -> Opc_AMO
| AMOSWAP_W_00_32A -> Opc_AMO
| AMOSWAP_W_01_32A -> Opc_AMO
| AMOSWAP_W_10_32A -> Opc_AMO
| AMOSWAP_W_11_32A -> Opc_AMO
| AMOADD_W_00_32A -> Opc_AMO
| AMOADD_W_01_32A -> Opc_AMO
| AMOADD_W_10_32A -> Opc_AMO
| AMOADD_W_11_32A -> Opc_AMO
| AMOXOR_W_00_32A -> Opc_AMO
| AMOXOR_W_01_32A -> Opc_AMO
| AMOXOR_W_10_32A -> Opc_AMO
| AMOXOR_W_11_32A -> Opc_AMO
| AMOAND_W_00_32A -> Opc_AMO
| AMOAND_W_01_32A -> Opc_AMO
| AMOAND_W_10_32A -> Opc_AMO
| AMOAND_W_11_32A -> Opc_AMO
| AMOOR_W_00_32A -> Opc_AMO
| AMOOR_W_01_32A -> Opc_AMO
| AMOOR_W_10_32A -> Opc_AMO
| AMOOR_W_11_32A -> Opc_AMO
| AMOMIN_W_00_32A -> Opc_AMO
| AMOMIN_W_01_32A -> Opc_AMO
| AMOMIN_W_10_32A -> Opc_AMO
| AMOMIN_W_11_32A -> Opc_AMO
| AMOMAX_W_00_32A -> Opc_AMO
| AMOMAX_W_01_32A -> Opc_AMO
| AMOMAX_W_10_32A -> Opc_AMO
| AMOMAX_W_11_32A -> Opc_AMO
| AMOMINU_W_00_32A -> Opc_AMO
| AMOMINU_W_01_32A -> Opc_AMO
| AMOMINU_W_10_32A -> Opc_AMO
| AMOMINU_W_11_32A -> Opc_AMO
| AMOMAXU_W_00_32A -> Opc_AMO
| AMOMAXU_W_01_32A -> Opc_AMO
| AMOMAXU_W_10_32A -> Opc_AMO
| AMOMAXU_W_11_32A -> Opc_AMO
| LR_W_00_64A -> Opc_AMO
| LR_W_01_64A -> Opc_AMO
| LR_W_10_64A -> Opc_AMO
| LR_W_11_64A -> Opc_AMO
| SC_W_00_64A -> Opc_AMO
| SC_W_01_64A -> Opc_AMO
| SC_W_10_64A -> Opc_AMO
| SC_W_11_64A -> Opc_AMO
| AMOSWAP_W_00_64A -> Opc_AMO
| AMOSWAP_W_01_64A -> Opc_AMO
| AMOSWAP_W_10_64A -> Opc_AMO
| AMOSWAP_W_11_64A -> Opc_AMO
| AMOADD_W_00_64A -> Opc_AMO
| AMOADD_W_01_64A -> Opc_AMO
| AMOADD_W_10_64A -> Opc_AMO
| AMOADD_W_11_64A -> Opc_AMO
| AMOXOR_W_00_64A -> Opc_AMO
| AMOXOR_W_01_64A -> Opc_AMO
| AMOXOR_W_10_64A -> Opc_AMO
| AMOXOR_W_11_64A -> Opc_AMO
| AMOAND_W_00_64A -> Opc_AMO
| AMOAND_W_01_64A -> Opc_AMO
| AMOAND_W_10_64A -> Opc_AMO
| AMOAND_W_11_64A -> Opc_AMO
| AMOOR_W_00_64A -> Opc_AMO
| AMOOR_W_01_64A -> Opc_AMO
| AMOOR_W_10_64A -> Opc_AMO
| AMOOR_W_11_64A -> Opc_AMO
| AMOMIN_W_00_64A -> Opc_AMO
| AMOMIN_W_01_64A -> Opc_AMO
| AMOMIN_W_10_64A -> Opc_AMO
| AMOMIN_W_11_64A -> Opc_AMO
| AMOMAX_W_00_64A -> Opc_AMO
| AMOMAX_W_01_64A -> Opc_AMO
| AMOMAX_W_10_64A -> Opc_AMO
| AMOMAX_W_11_64A -> Opc_AMO
| AMOMINU_W_00_64A -> Opc_AMO
| AMOMINU_W_01_64A -> Opc_AMO
| AMOMINU_W_10_64A -> Opc_AMO
| AMOMINU_W_11_64A -> Opc_AMO
| AMOMAXU_W_00_64A -> Opc_AMO
| AMOMAXU_W_01_64A -> Opc_AMO
| AMOMAXU_W_10_64A -> Opc_AMO
| AMOMAXU_W_11_64A -> Opc_AMO
| LR_D_00_64A -> Opc_AMO
| LR_D_01_64A -> Opc_AMO
| LR_D_10_64A -> Opc_AMO
| LR_D_11_64A -> Opc_AMO
| SC_D_00_64A -> Opc_AMO
| SC_D_01_64A -> Opc_AMO
| SC_D_10_64A -> Opc_AMO
| SC_D_11_64A -> Opc_AMO
| AMOSWAP_D_00_64A -> Opc_AMO
| AMOSWAP_D_01_64A -> Opc_AMO
| AMOSWAP_D_10_64A -> Opc_AMO
| AMOSWAP_D_11_64A -> Opc_AMO
| AMOADD_D_00_64A -> Opc_AMO
| AMOADD_D_01_64A -> Opc_AMO
| AMOADD_D_10_64A -> Opc_AMO
| AMOADD_D_11_64A -> Opc_AMO
| AMOXOR_D_00_64A -> Opc_AMO
| AMOXOR_D_01_64A -> Opc_AMO
| AMOXOR_D_10_64A -> Opc_AMO
| AMOXOR_D_11_64A -> Opc_AMO
| AMOAND_D_00_64A -> Opc_AMO
| AMOAND_D_01_64A -> Opc_AMO
| AMOAND_D_10_64A -> Opc_AMO
| AMOAND_D_11_64A -> Opc_AMO
| AMOOR_D_00_64A -> Opc_AMO
| AMOOR_D_01_64A -> Opc_AMO
| AMOOR_D_10_64A -> Opc_AMO
| AMOOR_D_11_64A -> Opc_AMO
| AMOMIN_D_00_64A -> Opc_AMO
| AMOMIN_D_01_64A -> Opc_AMO
| AMOMIN_D_10_64A -> Opc_AMO
| AMOMIN_D_11_64A -> Opc_AMO
| AMOMAX_D_00_64A -> Opc_AMO
| AMOMAX_D_01_64A -> Opc_AMO
| AMOMAX_D_10_64A -> Opc_AMO
| AMOMAX_D_11_64A -> Opc_AMO
| AMOMINU_D_00_64A -> Opc_AMO
| AMOMINU_D_01_64A -> Opc_AMO
| AMOMINU_D_10_64A -> Opc_AMO
| AMOMINU_D_11_64A -> Opc_AMO
| AMOMAXU_D_00_64A -> Opc_AMO
| AMOMAXU_D_01_64A -> Opc_AMO
| AMOMAXU_D_10_64A -> Opc_AMO
| AMOMAXU_D_11_64A -> Opc_AMO
| FLW_32F -> Opc_LOAD_FP
| FSW_32F -> Opc_STORE_FP
| FMADD_RNE_S_32F -> Opc_MADD
| FMADD_RTZ_S_32F -> Opc_MADD
| FMADD_RDN_S_32F -> Opc_MADD
| FMADD_RUP_S_32F -> Opc_MADD
| FMADD_RMM_S_32F -> Opc_MADD
| FMADD_DYN_S_32F -> Opc_MADD
| FMSUB_RNE_S_32F -> Opc_MSUB
| FMSUB_RTZ_S_32F -> Opc_MSUB
| FMSUB_RDN_S_32F -> Opc_MSUB
| FMSUB_RUP_S_32F -> Opc_MSUB
| FMSUB_RMM_S_32F -> Opc_MSUB
| FMSUB_DYN_S_32F -> Opc_MSUB
| FNMSUB_RNE_S_32F -> Opc_NMSUB
| FNMSUB_RTZ_S_32F -> Opc_NMSUB
| FNMSUB_RDN_S_32F -> Opc_NMSUB
| FNMSUB_RUP_S_32F -> Opc_NMSUB
| FNMSUB_RMM_S_32F -> Opc_NMSUB
| FNMSUB_DYN_S_32F -> Opc_NMSUB
| FNMADD_RNE_S_32F -> Opc_NMADD
| FNMADD_RTZ_S_32F -> Opc_NMADD
| FNMADD_RDN_S_32F -> Opc_NMADD
| FNMADD_RUP_S_32F -> Opc_NMADD
| FNMADD_RMM_S_32F -> Opc_NMADD
| FNMADD_DYN_S_32F -> Opc_NMADD
| FLW_64F -> Opc_LOAD_FP
| FSW_64F -> Opc_LOAD_FP
| FMADD_RNE_S_64F -> Opc_MADD
| FMADD_RTZ_S_64F -> Opc_MADD
| FMADD_RDN_S_64F -> Opc_MADD
| FMADD_RUP_S_64F -> Opc_MADD
| FMADD_RMM_S_64F -> Opc_MADD
| FMADD_DYN_S_64F -> Opc_MADD
| FMSUB_RNE_S_64F -> Opc_MSUB
| FMSUB_RTZ_S_64F -> Opc_MSUB
| FMSUB_RDN_S_64F -> Opc_MSUB
| FMSUB_RUP_S_64F -> Opc_MSUB
| FMSUB_RMM_S_64F -> Opc_MSUB
| FMSUB_DYN_S_64F -> Opc_MSUB
| FNMSUB_RNE_S_64F -> Opc_NMSUB
| FNMSUB_RTZ_S_64F -> Opc_NMSUB
| FNMSUB_RDN_S_64F -> Opc_NMSUB
| FNMSUB_RUP_S_64F -> Opc_NMSUB
| FNMSUB_RMM_S_64F -> Opc_NMSUB
| FNMSUB_DYN_S_64F -> Opc_NMSUB
| FNMADD_RNE_S_64F -> Opc_NMADD
| FNMADD_RTZ_S_64F -> Opc_NMADD
| FNMADD_RDN_S_64F -> Opc_NMADD
| FNMADD_RUP_S_64F -> Opc_NMADD
| FNMADD_RMM_S_64F -> Opc_NMADD
| FNMADD_DYN_S_64F -> Opc_NMADD
| FLD_32D -> Opc_LOAD_FP
| FSD_32D -> Opc_STORE_FP
| FMADD_RNE_D_32D -> Opc_MADD
| FMADD_RTZ_D_32D -> Opc_MADD
| FMADD_RDN_D_32D -> Opc_MADD
| FMADD_RUP_D_32D -> Opc_MADD
| FMADD_RMM_D_32D -> Opc_MADD
| FMADD_DYN_D_32D -> Opc_MADD
| FMSUB_RNE_D_32D -> Opc_MSUB
| FMSUB_RTZ_D_32D -> Opc_MSUB
| FMSUB_RDN_D_32D -> Opc_MSUB
| FMSUB_RUP_D_32D -> Opc_MSUB
| FMSUB_RMM_D_32D -> Opc_MSUB
| FMSUB_DYN_D_32D -> Opc_MSUB
| FNMSUB_RNE_D_32D -> Opc_NMSUB
| FNMSUB_RTZ_D_32D -> Opc_NMSUB
| FNMSUB_RDN_D_32D -> Opc_NMSUB
| FNMSUB_RUP_D_32D -> Opc_NMSUB
| FNMSUB_RMM_D_32D -> Opc_NMSUB
| FNMSUB_DYN_D_32D -> Opc_NMSUB
| FNMADD_RNE_D_32D -> Opc_NMADD
| FNMADD_RTZ_D_32D -> Opc_NMADD
| FNMADD_RDN_D_32D -> Opc_NMADD
| FNMADD_RUP_D_32D -> Opc_NMADD
| FNMADD_RMM_D_32D -> Opc_NMADD
| FNMADD_DYN_D_32D -> Opc_NMADD
| FLD_64D -> Opc_LOAD_FP
| FSD_64D -> Opc_STORE_FP
| FMADD_RNE_D_64D -> Opc_MADD
| FMADD_RTZ_D_64D -> Opc_MADD
| FMADD_RDN_D_64D -> Opc_MADD
| FMADD_RUP_D_64D -> Opc_MADD
| FMADD_RMM_D_64D -> Opc_MADD
| FMADD_DYN_D_64D -> Opc_MADD
| FMSUB_RNE_D_64D -> Opc_MSUB
| FMSUB_RTZ_D_64D -> Opc_MSUB
| FMSUB_RDN_D_64D -> Opc_MSUB
| FMSUB_RUP_D_64D -> Opc_MSUB
| FMSUB_RMM_D_64D -> Opc_MSUB
| FMSUB_DYN_D_64D -> Opc_MSUB
| FNMSUB_RNE_D_64D -> Opc_NMSUB
| FNMSUB_RTZ_D_64D -> Opc_NMSUB
| FNMSUB_RDN_D_64D -> Opc_NMSUB
| FNMSUB_RUP_D_64D -> Opc_NMSUB
| FNMSUB_RMM_D_64D -> Opc_NMSUB
| FNMSUB_DYN_D_64D -> Opc_NMSUB
| FNMADD_RNE_D_64D -> Opc_NMADD
| FNMADD_RTZ_D_64D -> Opc_NMADD
| FNMADD_RDN_D_64D -> Opc_NMADD
| FNMADD_RUP_D_64D -> Opc_NMADD
| FNMADD_RMM_D_64D -> Opc_NMADD
| FNMADD_DYN_D_64D -> Opc_NMADD
| FLQ_32Q -> Opc_LOAD_FP
| FSQ_32Q -> Opc_STORE_FP
| FMADD_RNE_Q_32Q -> Opc_MADD
| FMADD_RTZ_Q_32Q -> Opc_MADD
| FMADD_RDN_Q_32Q -> Opc_MADD
| FMADD_RUP_Q_32Q -> Opc_MADD
| FMADD_RMM_Q_32Q -> Opc_MADD
| FMADD_DYN_Q_32Q -> Opc_MADD
| FMSUB_RNE_Q_32Q -> Opc_MSUB
| FMSUB_RTZ_Q_32Q -> Opc_MSUB
| FMSUB_RDN_Q_32Q -> Opc_MSUB
| FMSUB_RUP_Q_32Q -> Opc_MSUB
| FMSUB_RMM_Q_32Q -> Opc_MSUB
| FMSUB_DYN_Q_32Q -> Opc_MSUB
| FNMSUB_RNE_Q_32Q -> Opc_NMSUB
| FNMSUB_RTZ_Q_32Q -> Opc_NMSUB
| FNMSUB_RDN_Q_32Q -> Opc_NMSUB
| FNMSUB_RUP_Q_32Q -> Opc_NMSUB
| FNMSUB_RMM_Q_32Q -> Opc_NMSUB
| FNMSUB_DYN_Q_32Q -> Opc_NMSUB
| FNMADD_RNE_Q_32Q -> Opc_NMADD
| FNMADD_RTZ_Q_32Q -> Opc_NMADD
| FNMADD_RDN_Q_32Q -> Opc_NMADD
| FNMADD_RUP_Q_32Q -> Opc_NMADD
| FNMADD_RMM_Q_32Q -> Opc_NMADD
| FNMADD_DYN_Q_32Q -> Opc_NMADD
| FLQ_64Q -> Opc_LOAD_FP
| FSQ_64Q -> Opc_STORE_FP
| FMADD_RNE_Q_64Q -> Opc_MADD
| FMADD_RTZ_Q_64Q -> Opc_MADD
| FMADD_RDN_Q_64Q -> Opc_MADD
| FMADD_RUP_Q_64Q -> Opc_MADD
| FMADD_RMM_Q_64Q -> Opc_MADD
| FMADD_DYN_Q_64Q -> Opc_MADD
| FMSUB_RNE_Q_64Q -> Opc_MSUB
| FMSUB_RTZ_Q_64Q -> Opc_MSUB
| FMSUB_RDN_Q_64Q -> Opc_MSUB
| FMSUB_RUP_Q_64Q -> Opc_MSUB
| FMSUB_RMM_Q_64Q -> Opc_MSUB
| FMSUB_DYN_Q_64Q -> Opc_MSUB
| FNMSUB_RNE_Q_64Q -> Opc_NMSUB
| FNMSUB_RTZ_Q_64Q -> Opc_NMSUB
| FNMSUB_RDN_Q_64Q -> Opc_NMSUB
| FNMSUB_RUP_Q_64Q -> Opc_NMSUB
| FNMSUB_RMM_Q_64Q -> Opc_NMSUB
| FNMSUB_DYN_Q_64Q -> Opc_NMSUB
| FNMADD_RNE_Q_64Q -> Opc_NMADD
| FNMADD_RTZ_Q_64Q -> Opc_NMADD
| FNMADD_RDN_Q_64Q -> Opc_NMADD
| FNMADD_RUP_Q_64Q -> Opc_NMADD
| FNMADD_RMM_Q_64Q -> Opc_NMADD
| FNMADD_DYN_Q_64Q -> Opc_NMADD
| _ -> Opc_OP_FP

(** val get_opcode_i_type : opcode_name -> i_type **)

let get_opcode_i_type = function
| Opc_OP -> RType
| Opc_STORE -> SType
| Opc_BRANCH -> BType
| Opc_LUI -> UType
| Opc_AUIPC -> UType
| Opc_JAL -> JType
| Opc_OP_32 -> RType
| Opc_AMO -> RType
| Opc_OP_FP -> RType
| Opc_MADD -> R4Type
| Opc_MSUB -> R4Type
| Opc_NMSUB -> R4Type
| Opc_NMADD -> R4Type
| Opc_STORE_FP -> SType
| _ -> IType

(** val get_instruction_i_type : instruction -> i_type **)

let get_instruction_i_type i =
  get_opcode_i_type (instruction_opcode i)

type fct2_type =
| Fct2_00
| Fct2_01
| Fct2_11

(** val fct2_bin : fct2_type -> (bool, (bool, __) vect_cons_t) vect_cons_t **)

let fct2_bin = function
| Fct2_00 ->
  Obj.magic vect_cons (Pervasives.succ 0) false
    (vect_cons 0 false (Obj.magic __))
| Fct2_01 ->
  Obj.magic vect_cons (Pervasives.succ 0) true
    (vect_cons 0 false (Obj.magic __))
| Fct2_11 ->
  Obj.magic vect_cons (Pervasives.succ 0) true
    (vect_cons 0 true (Obj.magic __))

(** val fct2_type_beq : fct2_type -> fct2_type -> bool **)

let rec fct2_type_beq x y =
  match x with
  | Fct2_00 -> (match y with
                | Fct2_00 -> true
                | _ -> false)
  | Fct2_01 -> (match y with
                | Fct2_01 -> true
                | _ -> false)
  | Fct2_11 -> (match y with
                | Fct2_11 -> true
                | _ -> false)

(** val instruction_fct2 : instruction -> fct2_type **)

let instruction_fct2 = function
| FMADD_RNE_S_32F -> Fct2_00
| FMADD_RTZ_S_32F -> Fct2_00
| FMADD_RDN_S_32F -> Fct2_00
| FMADD_RUP_S_32F -> Fct2_00
| FMADD_RMM_S_32F -> Fct2_00
| FMADD_DYN_S_32F -> Fct2_00
| FMSUB_RNE_S_32F -> Fct2_00
| FMSUB_RTZ_S_32F -> Fct2_00
| FMSUB_RDN_S_32F -> Fct2_00
| FMSUB_RUP_S_32F -> Fct2_00
| FMSUB_RMM_S_32F -> Fct2_00
| FMSUB_DYN_S_32F -> Fct2_00
| FNMSUB_RNE_S_32F -> Fct2_00
| FNMSUB_RTZ_S_32F -> Fct2_00
| FNMSUB_RDN_S_32F -> Fct2_00
| FNMSUB_RUP_S_32F -> Fct2_00
| FNMSUB_RMM_S_32F -> Fct2_00
| FNMSUB_DYN_S_32F -> Fct2_00
| FNMADD_RNE_S_32F -> Fct2_00
| FNMADD_RTZ_S_32F -> Fct2_00
| FNMADD_RDN_S_32F -> Fct2_00
| FNMADD_RUP_S_32F -> Fct2_00
| FNMADD_RMM_S_32F -> Fct2_00
| FNMADD_DYN_S_32F -> Fct2_00
| FMADD_RNE_S_64F -> Fct2_00
| FMADD_RTZ_S_64F -> Fct2_00
| FMADD_RDN_S_64F -> Fct2_00
| FMADD_RUP_S_64F -> Fct2_00
| FMADD_RMM_S_64F -> Fct2_00
| FMADD_DYN_S_64F -> Fct2_00
| FMSUB_RNE_S_64F -> Fct2_00
| FMSUB_RTZ_S_64F -> Fct2_00
| FMSUB_RDN_S_64F -> Fct2_00
| FMSUB_RUP_S_64F -> Fct2_00
| FMSUB_RMM_S_64F -> Fct2_00
| FMSUB_DYN_S_64F -> Fct2_00
| FNMSUB_RNE_S_64F -> Fct2_00
| FNMSUB_RTZ_S_64F -> Fct2_00
| FNMSUB_RDN_S_64F -> Fct2_00
| FNMSUB_RUP_S_64F -> Fct2_00
| FNMSUB_RMM_S_64F -> Fct2_00
| FNMSUB_DYN_S_64F -> Fct2_00
| FNMADD_RNE_S_64F -> Fct2_00
| FNMADD_RTZ_S_64F -> Fct2_00
| FNMADD_RDN_S_64F -> Fct2_00
| FNMADD_RUP_S_64F -> Fct2_00
| FNMADD_RMM_S_64F -> Fct2_00
| FNMADD_DYN_S_64F -> Fct2_00
| FMADD_RNE_D_32D -> Fct2_01
| FMADD_RTZ_D_32D -> Fct2_01
| FMADD_RDN_D_32D -> Fct2_01
| FMADD_RUP_D_32D -> Fct2_01
| FMADD_RMM_D_32D -> Fct2_01
| FMADD_DYN_D_32D -> Fct2_01
| FMSUB_RNE_D_32D -> Fct2_01
| FMSUB_RTZ_D_32D -> Fct2_01
| FMSUB_RDN_D_32D -> Fct2_01
| FMSUB_RUP_D_32D -> Fct2_01
| FMSUB_RMM_D_32D -> Fct2_01
| FMSUB_DYN_D_32D -> Fct2_01
| FNMSUB_RNE_D_32D -> Fct2_01
| FNMSUB_RTZ_D_32D -> Fct2_01
| FNMSUB_RDN_D_32D -> Fct2_01
| FNMSUB_RUP_D_32D -> Fct2_01
| FNMSUB_RMM_D_32D -> Fct2_01
| FNMSUB_DYN_D_32D -> Fct2_01
| FNMADD_RNE_D_32D -> Fct2_01
| FNMADD_RTZ_D_32D -> Fct2_01
| FNMADD_RDN_D_32D -> Fct2_01
| FNMADD_RUP_D_32D -> Fct2_01
| FNMADD_RMM_D_32D -> Fct2_01
| FNMADD_DYN_D_32D -> Fct2_01
| FMADD_RNE_D_64D -> Fct2_01
| FMADD_RTZ_D_64D -> Fct2_01
| FMADD_RDN_D_64D -> Fct2_01
| FMADD_RUP_D_64D -> Fct2_01
| FMADD_RMM_D_64D -> Fct2_01
| FMADD_DYN_D_64D -> Fct2_01
| FMSUB_RNE_D_64D -> Fct2_01
| FMSUB_RTZ_D_64D -> Fct2_01
| FMSUB_RDN_D_64D -> Fct2_01
| FMSUB_RUP_D_64D -> Fct2_01
| FMSUB_RMM_D_64D -> Fct2_01
| FMSUB_DYN_D_64D -> Fct2_01
| FNMSUB_RNE_D_64D -> Fct2_01
| FNMSUB_RTZ_D_64D -> Fct2_01
| FNMSUB_RDN_D_64D -> Fct2_01
| FNMSUB_RUP_D_64D -> Fct2_01
| FNMSUB_RMM_D_64D -> Fct2_01
| FNMSUB_DYN_D_64D -> Fct2_01
| FNMADD_RNE_D_64D -> Fct2_01
| FNMADD_RTZ_D_64D -> Fct2_01
| FNMADD_RDN_D_64D -> Fct2_01
| FNMADD_RUP_D_64D -> Fct2_01
| FNMADD_RMM_D_64D -> Fct2_01
| FNMADD_DYN_D_64D -> Fct2_01
| FMADD_RNE_Q_32Q -> Fct2_11
| FMADD_RTZ_Q_32Q -> Fct2_11
| FMADD_RDN_Q_32Q -> Fct2_11
| FMADD_RUP_Q_32Q -> Fct2_11
| FMADD_RMM_Q_32Q -> Fct2_11
| FMADD_DYN_Q_32Q -> Fct2_11
| FMSUB_RNE_Q_32Q -> Fct2_11
| FMSUB_RTZ_Q_32Q -> Fct2_11
| FMSUB_RDN_Q_32Q -> Fct2_11
| FMSUB_RUP_Q_32Q -> Fct2_11
| FMSUB_RMM_Q_32Q -> Fct2_11
| FMSUB_DYN_Q_32Q -> Fct2_11
| FNMSUB_RNE_Q_32Q -> Fct2_11
| FNMSUB_RTZ_Q_32Q -> Fct2_11
| FNMSUB_RDN_Q_32Q -> Fct2_11
| FNMSUB_RUP_Q_32Q -> Fct2_11
| FNMSUB_RMM_Q_32Q -> Fct2_11
| FNMSUB_DYN_Q_32Q -> Fct2_11
| FNMADD_RNE_Q_32Q -> Fct2_11
| FNMADD_RTZ_Q_32Q -> Fct2_11
| FNMADD_RDN_Q_32Q -> Fct2_11
| FNMADD_RUP_Q_32Q -> Fct2_11
| FNMADD_RMM_Q_32Q -> Fct2_11
| FNMADD_DYN_Q_32Q -> Fct2_11
| FMADD_RNE_Q_64Q -> Fct2_11
| FMADD_RTZ_Q_64Q -> Fct2_11
| FMADD_RDN_Q_64Q -> Fct2_11
| FMADD_RUP_Q_64Q -> Fct2_11
| FMADD_RMM_Q_64Q -> Fct2_11
| FMADD_DYN_Q_64Q -> Fct2_11
| FMSUB_RNE_Q_64Q -> Fct2_11
| FMSUB_RTZ_Q_64Q -> Fct2_11
| FMSUB_RDN_Q_64Q -> Fct2_11
| FMSUB_RUP_Q_64Q -> Fct2_11
| FMSUB_RMM_Q_64Q -> Fct2_11
| FMSUB_DYN_Q_64Q -> Fct2_11
| FNMSUB_RNE_Q_64Q -> Fct2_11
| FNMSUB_RTZ_Q_64Q -> Fct2_11
| FNMSUB_RDN_Q_64Q -> Fct2_11
| FNMSUB_RUP_Q_64Q -> Fct2_11
| FNMSUB_RMM_Q_64Q -> Fct2_11
| FNMSUB_DYN_Q_64Q -> Fct2_11
| FNMADD_RNE_Q_64Q -> Fct2_11
| FNMADD_RTZ_Q_64Q -> Fct2_11
| FNMADD_RDN_Q_64Q -> Fct2_11
| FNMADD_RUP_Q_64Q -> Fct2_11
| FNMADD_RMM_Q_64Q -> Fct2_11
| FNMADD_DYN_Q_64Q -> Fct2_11
| _ -> assert false (* absurd case *)

type fct3_type =
| Fct3_000
| Fct3_001
| Fct3_010
| Fct3_011
| Fct3_100
| Fct3_101
| Fct3_110
| Fct3_111

(** val fct3_type_beq : fct3_type -> fct3_type -> bool **)

let rec fct3_type_beq x y =
  match x with
  | Fct3_000 -> (match y with
                 | Fct3_000 -> true
                 | _ -> false)
  | Fct3_001 -> (match y with
                 | Fct3_001 -> true
                 | _ -> false)
  | Fct3_010 -> (match y with
                 | Fct3_010 -> true
                 | _ -> false)
  | Fct3_011 -> (match y with
                 | Fct3_011 -> true
                 | _ -> false)
  | Fct3_100 -> (match y with
                 | Fct3_100 -> true
                 | _ -> false)
  | Fct3_101 -> (match y with
                 | Fct3_101 -> true
                 | _ -> false)
  | Fct3_110 -> (match y with
                 | Fct3_110 -> true
                 | _ -> false)
  | Fct3_111 -> (match y with
                 | Fct3_111 -> true
                 | _ -> false)

(** val fct3_bin :
    fct3_type -> (bool, (bool, (bool, __) vect_cons_t) vect_cons_t)
    vect_cons_t **)

let fct3_bin = function
| Fct3_000 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
    (vect_cons (Pervasives.succ 0) false (Obj.magic vect_cons 0 false __))
| Fct3_001 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
    (vect_cons (Pervasives.succ 0) false (Obj.magic vect_cons 0 false __))
| Fct3_010 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
    (vect_cons (Pervasives.succ 0) true (Obj.magic vect_cons 0 false __))
| Fct3_011 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
    (vect_cons (Pervasives.succ 0) true (Obj.magic vect_cons 0 false __))
| Fct3_100 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
    (vect_cons (Pervasives.succ 0) false (Obj.magic vect_cons 0 true __))
| Fct3_101 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
    (vect_cons (Pervasives.succ 0) false (Obj.magic vect_cons 0 true __))
| Fct3_110 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
    (vect_cons (Pervasives.succ 0) true (Obj.magic vect_cons 0 true __))
| Fct3_111 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
    (vect_cons (Pervasives.succ 0) true (Obj.magic vect_cons 0 true __))

(** val instruction_fct3 : instruction -> fct3_type **)

let instruction_fct3 = function
| LUI_32I -> assert false (* absurd case *)
| AUIPC_32I -> assert false (* absurd case *)
| JAL_32I -> assert false (* absurd case *)
| JALR_32I -> Fct3_000
| BEQ_32I -> Fct3_000
| BNE_32I -> Fct3_001
| BLT_32I -> Fct3_100
| BGE_32I -> Fct3_101
| BLTU_32I -> Fct3_110
| BGEU_32I -> Fct3_111
| LB_32I -> Fct3_000
| LH_32I -> Fct3_001
| LBU_32I -> Fct3_100
| LHU_32I -> Fct3_101
| SB_32I -> Fct3_000
| SH_32I -> Fct3_001
| ADDI_32I -> Fct3_000
| SLTIU_32I -> Fct3_011
| XORI_32I -> Fct3_100
| ORI_32I -> Fct3_110
| ANDI_32I -> Fct3_111
| SLLI_32I -> Fct3_001
| SRLI_32I -> Fct3_101
| SRAI_32I -> Fct3_101
| ADD_32I -> Fct3_000
| SUB_32I -> Fct3_000
| SLL_32I -> Fct3_001
| SLTU_32I -> Fct3_011
| XOR_32I -> Fct3_100
| SRL_32I -> Fct3_101
| SRA_32I -> Fct3_101
| OR_32I -> Fct3_110
| AND_32I -> Fct3_111
| FENCE_32I -> Fct3_000
| ECALL_32I -> Fct3_000
| EBREAK_32I -> Fct3_000
| LUI_64I -> assert false (* absurd case *)
| AUIPC_64I -> assert false (* absurd case *)
| JAL_64I -> assert false (* absurd case *)
| JALR_64I -> Fct3_000
| BEQ_64I -> Fct3_000
| BNE_64I -> Fct3_001
| BLT_64I -> Fct3_100
| BGE_64I -> Fct3_101
| BLTU_64I -> Fct3_110
| BGEU_64I -> Fct3_111
| LB_64I -> Fct3_000
| LH_64I -> Fct3_001
| LBU_64I -> Fct3_100
| LHU_64I -> Fct3_101
| SB_64I -> Fct3_000
| SH_64I -> Fct3_001
| ADDI_64I -> Fct3_000
| SLTIU_64I -> Fct3_011
| XORI_64I -> Fct3_100
| ORI_64I -> Fct3_110
| ANDI_64I -> Fct3_111
| SLLI_64I -> Fct3_001
| SRLI_64I -> Fct3_101
| SRAI_64I -> Fct3_101
| ADD_64I -> Fct3_000
| SUB_64I -> Fct3_000
| SLL_64I -> Fct3_001
| SLTU_64I -> Fct3_011
| XOR_64I -> Fct3_100
| SRL_64I -> Fct3_101
| SRA_64I -> Fct3_101
| OR_64I -> Fct3_110
| AND_64I -> Fct3_111
| FENCE_64I -> Fct3_000
| ECALL_64I -> Fct3_000
| EBREAK_64I -> Fct3_000
| LWU_64I -> Fct3_110
| LD_64I -> Fct3_011
| SD_64I -> Fct3_011
| ADDIW_64I -> Fct3_000
| SLLIW_64I -> Fct3_001
| SRLIW_64I -> Fct3_101
| SRAIW_64I -> Fct3_101
| ADDW_64I -> Fct3_000
| SUBW_64I -> Fct3_000
| SLLW_64I -> Fct3_001
| SRLW_64I -> Fct3_101
| SRAW_64I -> Fct3_101
| FENCE_I_32Zifencei -> Fct3_001
| FENCE_I_64Zifencei -> Fct3_001
| CSRRW_32Zicsr -> Fct3_001
| CSRRC_32Zicsr -> Fct3_011
| CSRRWI_32Zicsr -> Fct3_101
| CSRRSI_32Zicsr -> Fct3_110
| CSRRCI_32Zicsr -> Fct3_111
| CSRRW_64Zicsr -> Fct3_001
| CSRRC_64Zicsr -> Fct3_011
| CSRRWI_64Zicsr -> Fct3_101
| CSRRSI_64Zicsr -> Fct3_110
| CSRRCI_64Zicsr -> Fct3_111
| MUL_32M -> Fct3_000
| MULH_32M -> Fct3_001
| MULHU_32M -> Fct3_011
| DIV_32M -> Fct3_100
| DIVU_32M -> Fct3_101
| REM_32M -> Fct3_110
| REMU_32M -> Fct3_111
| MUL_64M -> Fct3_000
| MULH_64M -> Fct3_001
| MULHU_64M -> Fct3_011
| DIV_64M -> Fct3_100
| DIVU_64M -> Fct3_101
| REM_64M -> Fct3_110
| REMU_64M -> Fct3_111
| MULW_64M -> Fct3_000
| DIVW_64M -> Fct3_100
| DIVUW_64M -> Fct3_101
| REMW_64M -> Fct3_110
| REMUW_64M -> Fct3_111
| LR_D_00_64A -> Fct3_011
| LR_D_01_64A -> Fct3_011
| LR_D_10_64A -> Fct3_011
| LR_D_11_64A -> Fct3_011
| SC_D_00_64A -> Fct3_011
| SC_D_01_64A -> Fct3_011
| SC_D_10_64A -> Fct3_011
| SC_D_11_64A -> Fct3_011
| AMOSWAP_D_00_64A -> Fct3_011
| AMOSWAP_D_01_64A -> Fct3_011
| AMOSWAP_D_10_64A -> Fct3_011
| AMOSWAP_D_11_64A -> Fct3_011
| AMOADD_D_00_64A -> Fct3_011
| AMOADD_D_01_64A -> Fct3_011
| AMOADD_D_10_64A -> Fct3_011
| AMOADD_D_11_64A -> Fct3_011
| AMOXOR_D_00_64A -> Fct3_011
| AMOXOR_D_01_64A -> Fct3_011
| AMOXOR_D_10_64A -> Fct3_011
| AMOXOR_D_11_64A -> Fct3_011
| AMOAND_D_00_64A -> Fct3_011
| AMOAND_D_01_64A -> Fct3_011
| AMOAND_D_10_64A -> Fct3_011
| AMOAND_D_11_64A -> Fct3_011
| AMOOR_D_00_64A -> Fct3_011
| AMOOR_D_01_64A -> Fct3_011
| AMOOR_D_10_64A -> Fct3_011
| AMOOR_D_11_64A -> Fct3_011
| AMOMIN_D_00_64A -> Fct3_011
| AMOMIN_D_01_64A -> Fct3_011
| AMOMIN_D_10_64A -> Fct3_011
| AMOMIN_D_11_64A -> Fct3_011
| AMOMAX_D_00_64A -> Fct3_011
| AMOMAX_D_01_64A -> Fct3_011
| AMOMAX_D_10_64A -> Fct3_011
| AMOMAX_D_11_64A -> Fct3_011
| AMOMINU_D_00_64A -> Fct3_011
| AMOMINU_D_01_64A -> Fct3_011
| AMOMINU_D_10_64A -> Fct3_011
| AMOMINU_D_11_64A -> Fct3_011
| AMOMAXU_D_00_64A -> Fct3_011
| AMOMAXU_D_01_64A -> Fct3_011
| AMOMAXU_D_10_64A -> Fct3_011
| AMOMAXU_D_11_64A -> Fct3_011
| FMADD_RNE_S_32F -> Fct3_000
| FMADD_RTZ_S_32F -> Fct3_001
| FMADD_RUP_S_32F -> Fct3_011
| FMADD_RMM_S_32F -> Fct3_100
| FMADD_DYN_S_32F -> Fct3_111
| FMSUB_RNE_S_32F -> Fct3_000
| FMSUB_RTZ_S_32F -> Fct3_001
| FMSUB_RUP_S_32F -> Fct3_011
| FMSUB_RMM_S_32F -> Fct3_100
| FMSUB_DYN_S_32F -> Fct3_111
| FNMSUB_RNE_S_32F -> Fct3_000
| FNMSUB_RTZ_S_32F -> Fct3_001
| FNMSUB_RUP_S_32F -> Fct3_011
| FNMSUB_RMM_S_32F -> Fct3_100
| FNMSUB_DYN_S_32F -> Fct3_111
| FNMADD_RNE_S_32F -> Fct3_000
| FNMADD_RTZ_S_32F -> Fct3_001
| FNMADD_RUP_S_32F -> Fct3_011
| FNMADD_RMM_S_32F -> Fct3_100
| FNMADD_DYN_S_32F -> Fct3_111
| FADD_RNE_S_32F -> Fct3_000
| FADD_RTZ_S_32F -> Fct3_001
| FADD_RUP_S_32F -> Fct3_011
| FADD_RMM_S_32F -> Fct3_100
| FADD_DYN_S_32F -> Fct3_111
| FSUB_RNE_S_32F -> Fct3_000
| FSUB_RTZ_S_32F -> Fct3_001
| FSUB_RUP_S_32F -> Fct3_011
| FSUB_RMM_S_32F -> Fct3_100
| FSUB_DYN_S_32F -> Fct3_111
| FMUL_RNE_S_32F -> Fct3_000
| FMUL_RTZ_S_32F -> Fct3_001
| FMUL_RUP_S_32F -> Fct3_011
| FMUL_RMM_S_32F -> Fct3_100
| FMUL_DYN_S_32F -> Fct3_111
| FDIV_RNE_S_32F -> Fct3_000
| FDIV_RTZ_S_32F -> Fct3_001
| FDIV_RUP_S_32F -> Fct3_011
| FDIV_RMM_S_32F -> Fct3_100
| FDIV_DYN_S_32F -> Fct3_111
| FSQRT_RNE_S_32F -> Fct3_000
| FSQRT_RTZ_S_32F -> Fct3_001
| FSQRT_RUP_S_32F -> Fct3_011
| FSQRT_RMM_S_32F -> Fct3_100
| FSQRT_DYN_S_32F -> Fct3_111
| FSGNJ_S_32F -> Fct3_000
| FSGNJN_S_32F -> Fct3_001
| FMIN_S_32F -> Fct3_000
| FMAX_S_32F -> Fct3_001
| FCVT_RNE_W_S_32F -> Fct3_000
| FCVT_RTZ_W_S_32F -> Fct3_001
| FCVT_RUP_W_S_32F -> Fct3_011
| FCVT_RMM_W_S_32F -> Fct3_100
| FCVT_DYN_W_S_32F -> Fct3_111
| FCVT_RNE_WU_S_32F -> Fct3_000
| FCVT_RTZ_WU_S_32F -> Fct3_001
| FCVT_RUP_WU_S_32F -> Fct3_011
| FCVT_RMM_WU_S_32F -> Fct3_100
| FCVT_DYN_WU_S_32F -> Fct3_111
| FMV_X_W_32F -> Fct3_000
| FLT_S_32F -> Fct3_001
| FLE_S_32F -> Fct3_000
| FCLASS_S_32F -> Fct3_001
| FCVT_RNE_S_W_32F -> Fct3_000
| FCVT_RTZ_S_W_32F -> Fct3_001
| FCVT_RUP_S_W_32F -> Fct3_011
| FCVT_RMM_S_W_32F -> Fct3_100
| FCVT_DYN_S_W_32F -> Fct3_111
| FCVT_RNE_S_WU_32F -> Fct3_000
| FCVT_RTZ_S_WU_32F -> Fct3_001
| FCVT_RUP_S_WU_32F -> Fct3_011
| FCVT_RMM_S_WU_32F -> Fct3_100
| FCVT_DYN_S_WU_32F -> Fct3_111
| FMV_W_X_32F -> Fct3_000
| FMADD_RNE_S_64F -> Fct3_000
| FMADD_RTZ_S_64F -> Fct3_001
| FMADD_RUP_S_64F -> Fct3_011
| FMADD_RMM_S_64F -> Fct3_100
| FMADD_DYN_S_64F -> Fct3_111
| FMSUB_RNE_S_64F -> Fct3_000
| FMSUB_RTZ_S_64F -> Fct3_001
| FMSUB_RUP_S_64F -> Fct3_011
| FMSUB_RMM_S_64F -> Fct3_100
| FMSUB_DYN_S_64F -> Fct3_111
| FNMSUB_RNE_S_64F -> Fct3_000
| FNMSUB_RTZ_S_64F -> Fct3_001
| FNMSUB_RUP_S_64F -> Fct3_011
| FNMSUB_RMM_S_64F -> Fct3_100
| FNMSUB_DYN_S_64F -> Fct3_111
| FNMADD_RNE_S_64F -> Fct3_000
| FNMADD_RTZ_S_64F -> Fct3_001
| FNMADD_RUP_S_64F -> Fct3_011
| FNMADD_RMM_S_64F -> Fct3_100
| FNMADD_DYN_S_64F -> Fct3_111
| FADD_RNE_S_64F -> Fct3_000
| FADD_RTZ_S_64F -> Fct3_001
| FADD_RUP_S_64F -> Fct3_011
| FADD_RMM_S_64F -> Fct3_100
| FADD_DYN_S_64F -> Fct3_111
| FSUB_RNE_S_64F -> Fct3_000
| FSUB_RTZ_S_64F -> Fct3_001
| FSUB_RUP_S_64F -> Fct3_011
| FSUB_RMM_S_64F -> Fct3_100
| FSUB_DYN_S_64F -> Fct3_111
| FMUL_RNE_S_64F -> Fct3_000
| FMUL_RTZ_S_64F -> Fct3_001
| FMUL_RUP_S_64F -> Fct3_011
| FMUL_RMM_S_64F -> Fct3_100
| FMUL_DYN_S_64F -> Fct3_111
| FDIV_RNE_S_64F -> Fct3_000
| FDIV_RTZ_S_64F -> Fct3_001
| FDIV_RUP_S_64F -> Fct3_011
| FDIV_RMM_S_64F -> Fct3_100
| FDIV_DYN_S_64F -> Fct3_111
| FSQRT_RNE_S_64F -> Fct3_000
| FSQRT_RTZ_S_64F -> Fct3_001
| FSQRT_RUP_S_64F -> Fct3_011
| FSQRT_RMM_S_64F -> Fct3_100
| FSQRT_DYN_S_64F -> Fct3_111
| FSGNJ_S_64F -> Fct3_000
| FSGNJN_S_64F -> Fct3_001
| FMIN_S_64F -> Fct3_000
| FMAX_S_64F -> Fct3_001
| FCVT_RNE_W_S_64F -> Fct3_000
| FCVT_RTZ_W_S_64F -> Fct3_001
| FCVT_RUP_W_S_64F -> Fct3_011
| FCVT_RMM_W_S_64F -> Fct3_100
| FCVT_DYN_W_S_64F -> Fct3_111
| FCVT_RNE_WU_S_64F -> Fct3_000
| FCVT_RTZ_WU_S_64F -> Fct3_001
| FCVT_RUP_WU_S_64F -> Fct3_011
| FCVT_RMM_WU_S_64F -> Fct3_100
| FCVT_DYN_WU_S_64F -> Fct3_111
| FMV_X_W_64F -> Fct3_000
| FLT_S_64F -> Fct3_001
| FLE_S_64F -> Fct3_000
| FCLASS_S_64F -> Fct3_001
| FCVT_RNE_S_W_64F -> Fct3_000
| FCVT_RTZ_S_W_64F -> Fct3_001
| FCVT_RUP_S_W_64F -> Fct3_011
| FCVT_RMM_S_W_64F -> Fct3_100
| FCVT_DYN_S_W_64F -> Fct3_111
| FCVT_RNE_S_WU_64F -> Fct3_000
| FCVT_RTZ_S_WU_64F -> Fct3_001
| FCVT_RUP_S_WU_64F -> Fct3_011
| FCVT_RMM_S_WU_64F -> Fct3_100
| FCVT_DYN_S_WU_64F -> Fct3_111
| FMV_W_X_64F -> Fct3_000
| FCVT_RNE_L_S_64F -> Fct3_000
| FCVT_RTZ_L_S_64F -> Fct3_001
| FCVT_RUP_L_S_64F -> Fct3_011
| FCVT_RMM_L_S_64F -> Fct3_100
| FCVT_DYN_L_S_64F -> Fct3_111
| FCVT_RNE_LU_S_64F -> Fct3_000
| FCVT_RTZ_LU_S_64F -> Fct3_001
| FCVT_RUP_LU_S_64F -> Fct3_011
| FCVT_RMM_LU_S_64F -> Fct3_100
| FCVT_DYN_LU_S_64F -> Fct3_111
| FCVT_RNE_S_L_64F -> Fct3_000
| FCVT_RTZ_S_L_64F -> Fct3_001
| FCVT_RUP_S_L_64F -> Fct3_011
| FCVT_RMM_S_L_64F -> Fct3_100
| FCVT_DYN_S_L_64F -> Fct3_111
| FCVT_RNE_S_LU_64F -> Fct3_000
| FCVT_RTZ_S_LU_64F -> Fct3_001
| FCVT_RUP_S_LU_64F -> Fct3_011
| FCVT_RMM_S_LU_64F -> Fct3_100
| FCVT_DYN_S_LU_64F -> Fct3_111
| FLD_32D -> Fct3_011
| FSD_32D -> Fct3_011
| FMADD_RNE_D_32D -> Fct3_000
| FMADD_RTZ_D_32D -> Fct3_001
| FMADD_RUP_D_32D -> Fct3_011
| FMADD_RMM_D_32D -> Fct3_100
| FMADD_DYN_D_32D -> Fct3_111
| FMSUB_RNE_D_32D -> Fct3_000
| FMSUB_RTZ_D_32D -> Fct3_001
| FMSUB_RUP_D_32D -> Fct3_011
| FMSUB_RMM_D_32D -> Fct3_100
| FMSUB_DYN_D_32D -> Fct3_111
| FNMSUB_RNE_D_32D -> Fct3_000
| FNMSUB_RTZ_D_32D -> Fct3_001
| FNMSUB_RUP_D_32D -> Fct3_011
| FNMSUB_RMM_D_32D -> Fct3_100
| FNMSUB_DYN_D_32D -> Fct3_111
| FNMADD_RNE_D_32D -> Fct3_000
| FNMADD_RTZ_D_32D -> Fct3_001
| FNMADD_RUP_D_32D -> Fct3_011
| FNMADD_RMM_D_32D -> Fct3_100
| FNMADD_DYN_D_32D -> Fct3_111
| FADD_RNE_D_32D -> Fct3_000
| FADD_RTZ_D_32D -> Fct3_001
| FADD_RUP_D_32D -> Fct3_011
| FADD_RMM_D_32D -> Fct3_100
| FADD_DYN_D_32D -> Fct3_111
| FSUB_RNE_D_32D -> Fct3_000
| FSUB_RTZ_D_32D -> Fct3_001
| FSUB_RUP_D_32D -> Fct3_011
| FSUB_RMM_D_32D -> Fct3_100
| FSUB_DYN_D_32D -> Fct3_111
| FMUL_RNE_D_32D -> Fct3_000
| FMUL_RTZ_D_32D -> Fct3_001
| FMUL_RUP_D_32D -> Fct3_011
| FMUL_RMM_D_32D -> Fct3_100
| FMUL_DYN_D_32D -> Fct3_111
| FDIV_RNE_D_32D -> Fct3_000
| FDIV_RTZ_D_32D -> Fct3_001
| FDIV_RUP_D_32D -> Fct3_011
| FDIV_RMM_D_32D -> Fct3_100
| FDIV_DYN_D_32D -> Fct3_111
| FSQRT_RNE_D_32D -> Fct3_000
| FSQRT_RTZ_D_32D -> Fct3_001
| FSQRT_RUP_D_32D -> Fct3_011
| FSQRT_RMM_D_32D -> Fct3_100
| FSQRT_DYN_D_32D -> Fct3_111
| FSGNJ_D_32D -> Fct3_000
| FSGNJN_D_32D -> Fct3_001
| FMIN_D_32D -> Fct3_000
| FMAX_D_32D -> Fct3_001
| FCVT_RNE_S_D_32D -> Fct3_000
| FCVT_RTZ_S_D_32D -> Fct3_001
| FCVT_RUP_S_D_32D -> Fct3_011
| FCVT_RMM_S_D_32D -> Fct3_100
| FCVT_DYN_S_D_32D -> Fct3_111
| FCVT_RNE_D_S_32D -> Fct3_000
| FCVT_RTZ_D_S_32D -> Fct3_001
| FCVT_RUP_D_S_32D -> Fct3_011
| FCVT_RMM_D_S_32D -> Fct3_100
| FCVT_DYN_D_S_32D -> Fct3_111
| FLT_D_32D -> Fct3_001
| FLE_D_32D -> Fct3_000
| FCLASS_D_32D -> Fct3_001
| FCVT_RNE_W_D_32D -> Fct3_000
| FCVT_RTZ_W_D_32D -> Fct3_001
| FCVT_RUP_W_D_32D -> Fct3_011
| FCVT_RMM_W_D_32D -> Fct3_100
| FCVT_DYN_W_D_32D -> Fct3_111
| FCVT_RNE_WU_D_32D -> Fct3_000
| FCVT_RTZ_WU_D_32D -> Fct3_001
| FCVT_RUP_WU_D_32D -> Fct3_011
| FCVT_RMM_WU_D_32D -> Fct3_100
| FCVT_DYN_WU_D_32D -> Fct3_111
| FCVT_RNE_D_W_32D -> Fct3_000
| FCVT_RTZ_D_W_32D -> Fct3_001
| FCVT_RUP_D_W_32D -> Fct3_011
| FCVT_RMM_D_W_32D -> Fct3_100
| FCVT_DYN_D_W_32D -> Fct3_111
| FCVT_RNE_D_WU_32D -> Fct3_000
| FCVT_RTZ_D_WU_32D -> Fct3_001
| FCVT_RUP_D_WU_32D -> Fct3_011
| FCVT_RMM_D_WU_32D -> Fct3_100
| FCVT_DYN_D_WU_32D -> Fct3_111
| FLD_64D -> Fct3_011
| FSD_64D -> Fct3_011
| FMADD_RNE_D_64D -> Fct3_000
| FMADD_RTZ_D_64D -> Fct3_001
| FMADD_RUP_D_64D -> Fct3_011
| FMADD_RMM_D_64D -> Fct3_100
| FMADD_DYN_D_64D -> Fct3_111
| FMSUB_RNE_D_64D -> Fct3_000
| FMSUB_RTZ_D_64D -> Fct3_001
| FMSUB_RUP_D_64D -> Fct3_011
| FMSUB_RMM_D_64D -> Fct3_100
| FMSUB_DYN_D_64D -> Fct3_111
| FNMSUB_RNE_D_64D -> Fct3_000
| FNMSUB_RTZ_D_64D -> Fct3_001
| FNMSUB_RUP_D_64D -> Fct3_011
| FNMSUB_RMM_D_64D -> Fct3_100
| FNMSUB_DYN_D_64D -> Fct3_111
| FNMADD_RNE_D_64D -> Fct3_000
| FNMADD_RTZ_D_64D -> Fct3_001
| FNMADD_RUP_D_64D -> Fct3_011
| FNMADD_RMM_D_64D -> Fct3_100
| FNMADD_DYN_D_64D -> Fct3_111
| FADD_RNE_D_64D -> Fct3_000
| FADD_RTZ_D_64D -> Fct3_001
| FADD_RUP_D_64D -> Fct3_011
| FADD_RMM_D_64D -> Fct3_100
| FADD_DYN_D_64D -> Fct3_111
| FSUB_RNE_D_64D -> Fct3_000
| FSUB_RTZ_D_64D -> Fct3_001
| FSUB_RUP_D_64D -> Fct3_011
| FSUB_RMM_D_64D -> Fct3_100
| FSUB_DYN_D_64D -> Fct3_111
| FMUL_RNE_D_64D -> Fct3_000
| FMUL_RTZ_D_64D -> Fct3_001
| FMUL_RUP_D_64D -> Fct3_011
| FMUL_RMM_D_64D -> Fct3_100
| FMUL_DYN_D_64D -> Fct3_111
| FDIV_RNE_D_64D -> Fct3_000
| FDIV_RTZ_D_64D -> Fct3_001
| FDIV_RUP_D_64D -> Fct3_011
| FDIV_RMM_D_64D -> Fct3_100
| FDIV_DYN_D_64D -> Fct3_111
| FSQRT_RNE_D_64D -> Fct3_000
| FSQRT_RTZ_D_64D -> Fct3_001
| FSQRT_RUP_D_64D -> Fct3_011
| FSQRT_RMM_D_64D -> Fct3_100
| FSQRT_DYN_D_64D -> Fct3_111
| FSGNJ_D_64D -> Fct3_000
| FSGNJN_D_64D -> Fct3_001
| FMIN_D_64D -> Fct3_000
| FMAX_D_64D -> Fct3_001
| FCVT_RNE_S_D_64D -> Fct3_000
| FCVT_RTZ_S_D_64D -> Fct3_001
| FCVT_RUP_S_D_64D -> Fct3_011
| FCVT_RMM_S_D_64D -> Fct3_100
| FCVT_DYN_S_D_64D -> Fct3_111
| FCVT_RNE_D_S_64D -> Fct3_000
| FCVT_RTZ_D_S_64D -> Fct3_001
| FCVT_RUP_D_S_64D -> Fct3_011
| FCVT_RMM_D_S_64D -> Fct3_100
| FCVT_DYN_D_S_64D -> Fct3_111
| FLT_D_64D -> Fct3_001
| FLE_D_64D -> Fct3_000
| FCLASS_D_64D -> Fct3_001
| FCVT_RNE_W_D_64D -> Fct3_000
| FCVT_RTZ_W_D_64D -> Fct3_001
| FCVT_RUP_W_D_64D -> Fct3_011
| FCVT_RMM_W_D_64D -> Fct3_100
| FCVT_DYN_W_D_64D -> Fct3_111
| FCVT_RNE_WU_D_64D -> Fct3_000
| FCVT_RTZ_WU_D_64D -> Fct3_001
| FCVT_RUP_WU_D_64D -> Fct3_011
| FCVT_RMM_WU_D_64D -> Fct3_100
| FCVT_DYN_WU_D_64D -> Fct3_111
| FCVT_RNE_D_W_64D -> Fct3_000
| FCVT_RTZ_D_W_64D -> Fct3_001
| FCVT_RUP_D_W_64D -> Fct3_011
| FCVT_RMM_D_W_64D -> Fct3_100
| FCVT_DYN_D_W_64D -> Fct3_111
| FCVT_RNE_D_WU_64D -> Fct3_000
| FCVT_RTZ_D_WU_64D -> Fct3_001
| FCVT_RUP_D_WU_64D -> Fct3_011
| FCVT_RMM_D_WU_64D -> Fct3_100
| FCVT_DYN_D_WU_64D -> Fct3_111
| FCVT_RNE_L_D_64D -> Fct3_000
| FCVT_RTZ_L_D_64D -> Fct3_001
| FCVT_RUP_L_D_64D -> Fct3_011
| FCVT_RMM_L_D_64D -> Fct3_100
| FCVT_DYN_L_D_64D -> Fct3_111
| FCVT_RNE_LU_D_64D -> Fct3_000
| FCVT_RTZ_LU_D_64D -> Fct3_001
| FCVT_RUP_LU_D_64D -> Fct3_011
| FCVT_RMM_LU_D_64D -> Fct3_100
| FCVT_DYN_LU_D_64D -> Fct3_111
| FMV_X_D_64D -> Fct3_000
| FCVT_RNE_D_L_64D -> Fct3_000
| FCVT_RTZ_D_L_64D -> Fct3_001
| FCVT_RUP_D_L_64D -> Fct3_011
| FCVT_RMM_D_L_64D -> Fct3_100
| FCVT_DYN_D_L_64D -> Fct3_111
| FCVT_RNE_D_LU_64D -> Fct3_000
| FCVT_RTZ_D_LU_64D -> Fct3_001
| FCVT_RUP_D_LU_64D -> Fct3_011
| FCVT_RMM_D_LU_64D -> Fct3_100
| FCVT_DYN_D_LU_64D -> Fct3_111
| FMV_D_X_64D -> Fct3_000
| FLQ_32Q -> Fct3_100
| FSQ_32Q -> Fct3_100
| FMADD_RNE_Q_32Q -> Fct3_000
| FMADD_RTZ_Q_32Q -> Fct3_001
| FMADD_RUP_Q_32Q -> Fct3_011
| FMADD_RMM_Q_32Q -> Fct3_100
| FMADD_DYN_Q_32Q -> Fct3_111
| FMSUB_RNE_Q_32Q -> Fct3_000
| FMSUB_RTZ_Q_32Q -> Fct3_001
| FMSUB_RUP_Q_32Q -> Fct3_011
| FMSUB_RMM_Q_32Q -> Fct3_100
| FMSUB_DYN_Q_32Q -> Fct3_111
| FNMSUB_RNE_Q_32Q -> Fct3_000
| FNMSUB_RTZ_Q_32Q -> Fct3_001
| FNMSUB_RUP_Q_32Q -> Fct3_011
| FNMSUB_RMM_Q_32Q -> Fct3_100
| FNMSUB_DYN_Q_32Q -> Fct3_111
| FNMADD_RNE_Q_32Q -> Fct3_000
| FNMADD_RTZ_Q_32Q -> Fct3_001
| FNMADD_RUP_Q_32Q -> Fct3_011
| FNMADD_RMM_Q_32Q -> Fct3_100
| FNMADD_DYN_Q_32Q -> Fct3_111
| FADD_RNE_Q_32Q -> Fct3_000
| FADD_RTZ_Q_32Q -> Fct3_001
| FADD_RUP_Q_32Q -> Fct3_011
| FADD_RMM_Q_32Q -> Fct3_100
| FADD_DYN_Q_32Q -> Fct3_111
| FSUB_RNE_Q_32Q -> Fct3_000
| FSUB_RTZ_Q_32Q -> Fct3_001
| FSUB_RUP_Q_32Q -> Fct3_011
| FSUB_RMM_Q_32Q -> Fct3_100
| FSUB_DYN_Q_32Q -> Fct3_111
| FMUL_RNE_Q_32Q -> Fct3_000
| FMUL_RTZ_Q_32Q -> Fct3_001
| FMUL_RUP_Q_32Q -> Fct3_011
| FMUL_RMM_Q_32Q -> Fct3_100
| FMUL_DYN_Q_32Q -> Fct3_111
| FDIV_RNE_Q_32Q -> Fct3_000
| FDIV_RTZ_Q_32Q -> Fct3_001
| FDIV_RUP_Q_32Q -> Fct3_011
| FDIV_RMM_Q_32Q -> Fct3_100
| FDIV_DYN_Q_32Q -> Fct3_111
| FSQRT_RNE_Q_32Q -> Fct3_000
| FSQRT_RTZ_Q_32Q -> Fct3_001
| FSQRT_RUP_Q_32Q -> Fct3_011
| FSQRT_RMM_Q_32Q -> Fct3_100
| FSQRT_DYN_Q_32Q -> Fct3_111
| FSGNJ_Q_32Q -> Fct3_000
| FSGNJN_Q_32Q -> Fct3_001
| FMIN_Q_32Q -> Fct3_000
| FMAX_Q_32Q -> Fct3_001
| FCVT_RNE_S_Q_32Q -> Fct3_000
| FCVT_RTZ_S_Q_32Q -> Fct3_001
| FCVT_RUP_S_Q_32Q -> Fct3_011
| FCVT_RMM_S_Q_32Q -> Fct3_100
| FCVT_DYN_S_Q_32Q -> Fct3_111
| FCVT_RNE_Q_S_32Q -> Fct3_000
| FCVT_RTZ_Q_S_32Q -> Fct3_001
| FCVT_RUP_Q_S_32Q -> Fct3_011
| FCVT_RMM_Q_S_32Q -> Fct3_100
| FCVT_DYN_Q_S_32Q -> Fct3_111
| FCVT_RNE_D_Q_32Q -> Fct3_000
| FCVT_RTZ_D_Q_32Q -> Fct3_001
| FCVT_RUP_D_Q_32Q -> Fct3_011
| FCVT_RMM_D_Q_32Q -> Fct3_100
| FCVT_DYN_D_Q_32Q -> Fct3_111
| FCVT_RNE_Q_D_32Q -> Fct3_000
| FCVT_RTZ_Q_D_32Q -> Fct3_001
| FCVT_RUP_Q_D_32Q -> Fct3_011
| FCVT_RMM_Q_D_32Q -> Fct3_100
| FCVT_DYN_Q_D_32Q -> Fct3_111
| FLT_Q_32Q -> Fct3_001
| FLE_Q_32Q -> Fct3_000
| FCLASS_Q_32Q -> Fct3_001
| FCVT_RNE_W_Q_32Q -> Fct3_000
| FCVT_RTZ_W_Q_32Q -> Fct3_001
| FCVT_RUP_W_Q_32Q -> Fct3_011
| FCVT_RMM_W_Q_32Q -> Fct3_100
| FCVT_DYN_W_Q_32Q -> Fct3_111
| FCVT_RNE_WU_Q_32Q -> Fct3_000
| FCVT_RTZ_WU_Q_32Q -> Fct3_001
| FCVT_RUP_WU_Q_32Q -> Fct3_011
| FCVT_RMM_WU_Q_32Q -> Fct3_100
| FCVT_DYN_WU_Q_32Q -> Fct3_111
| FCVT_RNE_Q_W_32Q -> Fct3_000
| FCVT_RTZ_Q_W_32Q -> Fct3_001
| FCVT_RUP_Q_W_32Q -> Fct3_011
| FCVT_RMM_Q_W_32Q -> Fct3_100
| FCVT_DYN_Q_W_32Q -> Fct3_111
| FCVT_RNE_Q_WU_32Q -> Fct3_000
| FCVT_RTZ_Q_WU_32Q -> Fct3_001
| FCVT_RUP_Q_WU_32Q -> Fct3_011
| FCVT_RMM_Q_WU_32Q -> Fct3_100
| FCVT_DYN_Q_WU_32Q -> Fct3_111
| FLQ_64Q -> Fct3_100
| FSQ_64Q -> Fct3_100
| FMADD_RNE_Q_64Q -> Fct3_000
| FMADD_RTZ_Q_64Q -> Fct3_001
| FMADD_RUP_Q_64Q -> Fct3_011
| FMADD_RMM_Q_64Q -> Fct3_100
| FMADD_DYN_Q_64Q -> Fct3_111
| FMSUB_RNE_Q_64Q -> Fct3_000
| FMSUB_RTZ_Q_64Q -> Fct3_001
| FMSUB_RUP_Q_64Q -> Fct3_011
| FMSUB_RMM_Q_64Q -> Fct3_100
| FMSUB_DYN_Q_64Q -> Fct3_111
| FNMSUB_RNE_Q_64Q -> Fct3_000
| FNMSUB_RTZ_Q_64Q -> Fct3_001
| FNMSUB_RUP_Q_64Q -> Fct3_011
| FNMSUB_RMM_Q_64Q -> Fct3_100
| FNMSUB_DYN_Q_64Q -> Fct3_111
| FNMADD_RNE_Q_64Q -> Fct3_000
| FNMADD_RTZ_Q_64Q -> Fct3_001
| FNMADD_RUP_Q_64Q -> Fct3_011
| FNMADD_RMM_Q_64Q -> Fct3_100
| FNMADD_DYN_Q_64Q -> Fct3_111
| FADD_RNE_Q_64Q -> Fct3_000
| FADD_RTZ_Q_64Q -> Fct3_001
| FADD_RUP_Q_64Q -> Fct3_011
| FADD_RMM_Q_64Q -> Fct3_100
| FADD_DYN_Q_64Q -> Fct3_111
| FSUB_RNE_Q_64Q -> Fct3_000
| FSUB_RTZ_Q_64Q -> Fct3_001
| FSUB_RUP_Q_64Q -> Fct3_011
| FSUB_RMM_Q_64Q -> Fct3_100
| FSUB_DYN_Q_64Q -> Fct3_111
| FMUL_RNE_Q_64Q -> Fct3_000
| FMUL_RTZ_Q_64Q -> Fct3_001
| FMUL_RUP_Q_64Q -> Fct3_011
| FMUL_RMM_Q_64Q -> Fct3_100
| FMUL_DYN_Q_64Q -> Fct3_111
| FDIV_RNE_Q_64Q -> Fct3_000
| FDIV_RTZ_Q_64Q -> Fct3_001
| FDIV_RUP_Q_64Q -> Fct3_011
| FDIV_RMM_Q_64Q -> Fct3_100
| FDIV_DYN_Q_64Q -> Fct3_111
| FSQRT_RNE_Q_64Q -> Fct3_000
| FSQRT_RTZ_Q_64Q -> Fct3_001
| FSQRT_RUP_Q_64Q -> Fct3_011
| FSQRT_RMM_Q_64Q -> Fct3_100
| FSQRT_DYN_Q_64Q -> Fct3_111
| FSGNJ_Q_64Q -> Fct3_000
| FSGNJN_Q_64Q -> Fct3_001
| FMIN_Q_64Q -> Fct3_000
| FMAX_Q_64Q -> Fct3_001
| FCVT_RNE_S_Q_64Q -> Fct3_000
| FCVT_RTZ_S_Q_64Q -> Fct3_001
| FCVT_RUP_S_Q_64Q -> Fct3_011
| FCVT_RMM_S_Q_64Q -> Fct3_100
| FCVT_DYN_S_Q_64Q -> Fct3_111
| FCVT_RNE_Q_S_64Q -> Fct3_000
| FCVT_RTZ_Q_S_64Q -> Fct3_001
| FCVT_RUP_Q_S_64Q -> Fct3_011
| FCVT_RMM_Q_S_64Q -> Fct3_100
| FCVT_DYN_Q_S_64Q -> Fct3_111
| FCVT_RNE_D_Q_64Q -> Fct3_000
| FCVT_RTZ_D_Q_64Q -> Fct3_001
| FCVT_RUP_D_Q_64Q -> Fct3_011
| FCVT_RMM_D_Q_64Q -> Fct3_100
| FCVT_DYN_D_Q_64Q -> Fct3_111
| FCVT_RNE_Q_D_64Q -> Fct3_000
| FCVT_RTZ_Q_D_64Q -> Fct3_001
| FCVT_RUP_Q_D_64Q -> Fct3_011
| FCVT_RMM_Q_D_64Q -> Fct3_100
| FCVT_DYN_Q_D_64Q -> Fct3_111
| FLT_Q_64Q -> Fct3_001
| FLE_Q_64Q -> Fct3_000
| FCLASS_Q_64Q -> Fct3_001
| FCVT_RNE_W_Q_64Q -> Fct3_000
| FCVT_RTZ_W_Q_64Q -> Fct3_001
| FCVT_RUP_W_Q_64Q -> Fct3_011
| FCVT_RMM_W_Q_64Q -> Fct3_100
| FCVT_DYN_W_Q_64Q -> Fct3_111
| FCVT_RNE_WU_Q_64Q -> Fct3_000
| FCVT_RTZ_WU_Q_64Q -> Fct3_001
| FCVT_RUP_WU_Q_64Q -> Fct3_011
| FCVT_RMM_WU_Q_64Q -> Fct3_100
| FCVT_DYN_WU_Q_64Q -> Fct3_111
| FCVT_RNE_Q_W_64Q -> Fct3_000
| FCVT_RTZ_Q_W_64Q -> Fct3_001
| FCVT_RUP_Q_W_64Q -> Fct3_011
| FCVT_RMM_Q_W_64Q -> Fct3_100
| FCVT_DYN_Q_W_64Q -> Fct3_111
| FCVT_RNE_Q_WU_64Q -> Fct3_000
| FCVT_RTZ_Q_WU_64Q -> Fct3_001
| FCVT_RUP_Q_WU_64Q -> Fct3_011
| FCVT_RMM_Q_WU_64Q -> Fct3_100
| FCVT_DYN_Q_WU_64Q -> Fct3_111
| FCVT_RNE_L_Q_64Q -> Fct3_000
| FCVT_RTZ_L_Q_64Q -> Fct3_001
| FCVT_RUP_L_Q_64Q -> Fct3_011
| FCVT_RMM_L_Q_64Q -> Fct3_100
| FCVT_DYN_L_Q_64Q -> Fct3_111
| FCVT_RNE_LU_Q_64Q -> Fct3_000
| FCVT_RTZ_LU_Q_64Q -> Fct3_001
| FCVT_RUP_LU_Q_64Q -> Fct3_011
| FCVT_RMM_LU_Q_64Q -> Fct3_100
| FCVT_DYN_LU_Q_64Q -> Fct3_111
| FCVT_RNE_Q_L_64Q -> Fct3_000
| FCVT_RTZ_Q_L_64Q -> Fct3_001
| FCVT_RUP_Q_L_64Q -> Fct3_011
| FCVT_RMM_Q_L_64Q -> Fct3_100
| FCVT_DYN_Q_L_64Q -> Fct3_111
| FCVT_RNE_Q_LU_64Q -> Fct3_000
| FCVT_RTZ_Q_LU_64Q -> Fct3_001
| FCVT_RUP_Q_LU_64Q -> Fct3_011
| FCVT_RMM_Q_LU_64Q -> Fct3_100
| FCVT_DYN_Q_LU_64Q -> Fct3_111
| _ -> Fct3_010

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

(** val fct7_type_beq : fct7_type -> fct7_type -> bool **)

let rec fct7_type_beq x y =
  match x with
  | Fct7_0000000 -> (match y with
                     | Fct7_0000000 -> true
                     | _ -> false)
  | Fct7_0000001 -> (match y with
                     | Fct7_0000001 -> true
                     | _ -> false)
  | Fct7_0000010 -> (match y with
                     | Fct7_0000010 -> true
                     | _ -> false)
  | Fct7_0000011 -> (match y with
                     | Fct7_0000011 -> true
                     | _ -> false)
  | Fct7_0000100 -> (match y with
                     | Fct7_0000100 -> true
                     | _ -> false)
  | Fct7_0000101 -> (match y with
                     | Fct7_0000101 -> true
                     | _ -> false)
  | Fct7_0000110 -> (match y with
                     | Fct7_0000110 -> true
                     | _ -> false)
  | Fct7_0000111 -> (match y with
                     | Fct7_0000111 -> true
                     | _ -> false)
  | Fct7_0001000 -> (match y with
                     | Fct7_0001000 -> true
                     | _ -> false)
  | Fct7_0001001 -> (match y with
                     | Fct7_0001001 -> true
                     | _ -> false)
  | Fct7_0001010 -> (match y with
                     | Fct7_0001010 -> true
                     | _ -> false)
  | Fct7_0001011 -> (match y with
                     | Fct7_0001011 -> true
                     | _ -> false)
  | Fct7_0001100 -> (match y with
                     | Fct7_0001100 -> true
                     | _ -> false)
  | Fct7_0001101 -> (match y with
                     | Fct7_0001101 -> true
                     | _ -> false)
  | Fct7_0001110 -> (match y with
                     | Fct7_0001110 -> true
                     | _ -> false)
  | Fct7_0001111 -> (match y with
                     | Fct7_0001111 -> true
                     | _ -> false)
  | Fct7_0010000 -> (match y with
                     | Fct7_0010000 -> true
                     | _ -> false)
  | Fct7_0010001 -> (match y with
                     | Fct7_0010001 -> true
                     | _ -> false)
  | Fct7_0010010 -> (match y with
                     | Fct7_0010010 -> true
                     | _ -> false)
  | Fct7_0010011 -> (match y with
                     | Fct7_0010011 -> true
                     | _ -> false)
  | Fct7_0010100 -> (match y with
                     | Fct7_0010100 -> true
                     | _ -> false)
  | Fct7_0010101 -> (match y with
                     | Fct7_0010101 -> true
                     | _ -> false)
  | Fct7_0010111 -> (match y with
                     | Fct7_0010111 -> true
                     | _ -> false)
  | Fct7_0100000 -> (match y with
                     | Fct7_0100000 -> true
                     | _ -> false)
  | Fct7_0100001 -> (match y with
                     | Fct7_0100001 -> true
                     | _ -> false)
  | Fct7_0100010 -> (match y with
                     | Fct7_0100010 -> true
                     | _ -> false)
  | Fct7_0100011 -> (match y with
                     | Fct7_0100011 -> true
                     | _ -> false)
  | Fct7_0101100 -> (match y with
                     | Fct7_0101100 -> true
                     | _ -> false)
  | Fct7_0101101 -> (match y with
                     | Fct7_0101101 -> true
                     | _ -> false)
  | Fct7_0101111 -> (match y with
                     | Fct7_0101111 -> true
                     | _ -> false)
  | Fct7_0110000 -> (match y with
                     | Fct7_0110000 -> true
                     | _ -> false)
  | Fct7_0110001 -> (match y with
                     | Fct7_0110001 -> true
                     | _ -> false)
  | Fct7_0110010 -> (match y with
                     | Fct7_0110010 -> true
                     | _ -> false)
  | Fct7_0110011 -> (match y with
                     | Fct7_0110011 -> true
                     | _ -> false)
  | Fct7_1000000 -> (match y with
                     | Fct7_1000000 -> true
                     | _ -> false)
  | Fct7_1000001 -> (match y with
                     | Fct7_1000001 -> true
                     | _ -> false)
  | Fct7_1000010 -> (match y with
                     | Fct7_1000010 -> true
                     | _ -> false)
  | Fct7_1000011 -> (match y with
                     | Fct7_1000011 -> true
                     | _ -> false)
  | Fct7_1010000 -> (match y with
                     | Fct7_1010000 -> true
                     | _ -> false)
  | Fct7_1010001 -> (match y with
                     | Fct7_1010001 -> true
                     | _ -> false)
  | Fct7_1010010 -> (match y with
                     | Fct7_1010010 -> true
                     | _ -> false)
  | Fct7_1010011 -> (match y with
                     | Fct7_1010011 -> true
                     | _ -> false)
  | Fct7_1100000 -> (match y with
                     | Fct7_1100000 -> true
                     | _ -> false)
  | Fct7_1100001 -> (match y with
                     | Fct7_1100001 -> true
                     | _ -> false)
  | Fct7_1100010 -> (match y with
                     | Fct7_1100010 -> true
                     | _ -> false)
  | Fct7_1100011 -> (match y with
                     | Fct7_1100011 -> true
                     | _ -> false)
  | Fct7_1101000 -> (match y with
                     | Fct7_1101000 -> true
                     | _ -> false)
  | Fct7_1101001 -> (match y with
                     | Fct7_1101001 -> true
                     | _ -> false)
  | Fct7_1101011 -> (match y with
                     | Fct7_1101011 -> true
                     | _ -> false)
  | Fct7_1110000 -> (match y with
                     | Fct7_1110000 -> true
                     | _ -> false)
  | Fct7_1110001 -> (match y with
                     | Fct7_1110001 -> true
                     | _ -> false)
  | Fct7_1110010 -> (match y with
                     | Fct7_1110010 -> true
                     | _ -> false)
  | Fct7_1110011 -> (match y with
                     | Fct7_1110011 -> true
                     | _ -> false)
  | Fct7_1111000 -> (match y with
                     | Fct7_1111000 -> true
                     | _ -> false)
  | Fct7_1111001 -> (match y with
                     | Fct7_1111001 -> true
                     | _ -> false)
  | Fct7_1111011 -> (match y with
                     | Fct7_1111011 -> true
                     | _ -> false)

(** val fct7_bin :
    fct7_type -> (bool, (bool, (bool, (bool, (bool, (bool, (bool, __)
    vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
    vect_cons_t) vect_cons_t **)

let fct7_bin = function
| Fct7_0000000 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0000001 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0000010 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0000011 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0000100 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0000101 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0000110 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0000111 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0001000 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0001001 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0001010 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0001011 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0001100 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0001101 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0001110 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0001111 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0010000 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0010001 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0010010 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0010011 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0010100 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0010101 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0010111 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0100000 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0100001 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0100010 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0100011 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0101100 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0101101 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0101111 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) true
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0110000 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0110001 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0110010 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 false __))))))
| Fct7_0110011 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 false __))))))
| Fct7_1000000 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1000001 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1000010 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1000011 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1010000 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1010001 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1010010 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1010011 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1100000 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1100001 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1100010 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1100011 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1101000 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1101001 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1101011 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1110000 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1110001 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1110010 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1110011 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          false
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1111000 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) false
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1111001 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) false
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 true __))))))
| Fct7_1111011 ->
  Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) true
    (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) true
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) false
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          true
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) true
              (Obj.magic vect_cons 0 true __))))))

(** val instruction_fct7 : instruction -> fct7_type **)

let instruction_fct7 = function
| ADD_32I -> Fct7_0000000
| SUB_32I -> Fct7_0100000
| SLL_32I -> Fct7_0000000
| SLT_32I -> Fct7_0000000
| SLTU_32I -> Fct7_0000000
| XOR_32I -> Fct7_0000000
| SRL_32I -> Fct7_0000000
| SRA_32I -> Fct7_0100000
| OR_32I -> Fct7_0000000
| AND_32I -> Fct7_0000000
| ADD_64I -> Fct7_0000000
| SUB_64I -> Fct7_0100000
| SLL_64I -> Fct7_0000000
| SLT_64I -> Fct7_0000000
| SLTU_64I -> Fct7_0000000
| XOR_64I -> Fct7_0000000
| SRL_64I -> Fct7_0000000
| SRA_64I -> Fct7_0100000
| OR_64I -> Fct7_0000000
| AND_64I -> Fct7_0000000
| ADDW_64I -> Fct7_0000000
| SUBW_64I -> Fct7_0100000
| SLLW_64I -> Fct7_0000000
| SRLW_64I -> Fct7_0000000
| SRAW_64I -> Fct7_0100000
| MUL_32M -> Fct7_0000001
| MULH_32M -> Fct7_0000001
| MULHSU_32M -> Fct7_0000001
| MULHU_32M -> Fct7_0000001
| DIV_32M -> Fct7_0000001
| DIVU_32M -> Fct7_0000001
| REM_32M -> Fct7_0000001
| REMU_32M -> Fct7_0000001
| MUL_64M -> Fct7_0000001
| MULH_64M -> Fct7_0000001
| MULHSU_64M -> Fct7_0000001
| MULHU_64M -> Fct7_0000001
| DIV_64M -> Fct7_0000001
| DIVU_64M -> Fct7_0000001
| REM_64M -> Fct7_0000001
| REMU_64M -> Fct7_0000001
| MULW_64M -> Fct7_0000001
| DIVW_64M -> Fct7_0000001
| DIVUW_64M -> Fct7_0000001
| REMW_64M -> Fct7_0000001
| REMUW_64M -> Fct7_0000001
| LR_W_00_32A -> Fct7_0001000
| LR_W_01_32A -> Fct7_0001001
| LR_W_10_32A -> Fct7_0001010
| LR_W_11_32A -> Fct7_0001011
| SC_W_00_32A -> Fct7_0001100
| SC_W_01_32A -> Fct7_0001101
| SC_W_10_32A -> Fct7_0001110
| SC_W_11_32A -> Fct7_0001111
| AMOSWAP_W_00_32A -> Fct7_0000100
| AMOSWAP_W_01_32A -> Fct7_0000101
| AMOSWAP_W_10_32A -> Fct7_0000110
| AMOSWAP_W_11_32A -> Fct7_0000111
| AMOADD_W_00_32A -> Fct7_0000000
| AMOADD_W_01_32A -> Fct7_0000001
| AMOADD_W_10_32A -> Fct7_0000010
| AMOADD_W_11_32A -> Fct7_0000011
| AMOXOR_W_00_32A -> Fct7_0010000
| AMOXOR_W_01_32A -> Fct7_0010001
| AMOXOR_W_10_32A -> Fct7_0010010
| AMOXOR_W_11_32A -> Fct7_0010011
| AMOAND_W_00_32A -> Fct7_0110000
| AMOAND_W_01_32A -> Fct7_0110001
| AMOAND_W_10_32A -> Fct7_0110010
| AMOAND_W_11_32A -> Fct7_0110011
| AMOOR_W_00_32A -> Fct7_0100000
| AMOOR_W_01_32A -> Fct7_0100001
| AMOOR_W_10_32A -> Fct7_0100010
| AMOOR_W_11_32A -> Fct7_0100011
| AMOMIN_W_00_32A -> Fct7_1000000
| AMOMIN_W_01_32A -> Fct7_1000001
| AMOMIN_W_10_32A -> Fct7_1000010
| AMOMIN_W_11_32A -> Fct7_1000011
| AMOMAX_W_00_32A -> Fct7_1010000
| AMOMAX_W_01_32A -> Fct7_1010001
| AMOMAX_W_10_32A -> Fct7_1010010
| AMOMAX_W_11_32A -> Fct7_1010011
| AMOMINU_W_00_32A -> Fct7_1100000
| AMOMINU_W_01_32A -> Fct7_1100001
| AMOMINU_W_10_32A -> Fct7_1100010
| AMOMINU_W_11_32A -> Fct7_1100011
| AMOMAXU_W_00_32A -> Fct7_1110000
| AMOMAXU_W_01_32A -> Fct7_1110001
| AMOMAXU_W_10_32A -> Fct7_1110010
| AMOMAXU_W_11_32A -> Fct7_1110011
| LR_W_00_64A -> Fct7_0001000
| LR_W_01_64A -> Fct7_0001001
| LR_W_10_64A -> Fct7_0001010
| LR_W_11_64A -> Fct7_0001011
| SC_W_00_64A -> Fct7_0001100
| SC_W_01_64A -> Fct7_0001101
| SC_W_10_64A -> Fct7_0001110
| SC_W_11_64A -> Fct7_0001111
| AMOSWAP_W_00_64A -> Fct7_0000100
| AMOSWAP_W_01_64A -> Fct7_0000101
| AMOSWAP_W_10_64A -> Fct7_0000110
| AMOSWAP_W_11_64A -> Fct7_0000111
| AMOADD_W_00_64A -> Fct7_0000000
| AMOADD_W_01_64A -> Fct7_0000001
| AMOADD_W_10_64A -> Fct7_0000010
| AMOADD_W_11_64A -> Fct7_0000011
| AMOXOR_W_00_64A -> Fct7_0010000
| AMOXOR_W_01_64A -> Fct7_0010001
| AMOXOR_W_10_64A -> Fct7_0010010
| AMOXOR_W_11_64A -> Fct7_0010011
| AMOAND_W_00_64A -> Fct7_0110000
| AMOAND_W_01_64A -> Fct7_0110001
| AMOAND_W_10_64A -> Fct7_0110010
| AMOAND_W_11_64A -> Fct7_0110011
| AMOOR_W_00_64A -> Fct7_0100000
| AMOOR_W_01_64A -> Fct7_0100001
| AMOOR_W_10_64A -> Fct7_0100010
| AMOOR_W_11_64A -> Fct7_0100011
| AMOMIN_W_00_64A -> Fct7_1000000
| AMOMIN_W_01_64A -> Fct7_1000001
| AMOMIN_W_10_64A -> Fct7_1000010
| AMOMIN_W_11_64A -> Fct7_1000011
| AMOMAX_W_00_64A -> Fct7_1010000
| AMOMAX_W_01_64A -> Fct7_1010001
| AMOMAX_W_10_64A -> Fct7_1010010
| AMOMAX_W_11_64A -> Fct7_1010011
| AMOMINU_W_00_64A -> Fct7_1100000
| AMOMINU_W_01_64A -> Fct7_1100001
| AMOMINU_W_10_64A -> Fct7_1100010
| AMOMINU_W_11_64A -> Fct7_1100011
| AMOMAXU_W_00_64A -> Fct7_1110000
| AMOMAXU_W_01_64A -> Fct7_1110001
| AMOMAXU_W_10_64A -> Fct7_1110010
| AMOMAXU_W_11_64A -> Fct7_1110011
| LR_D_00_64A -> Fct7_0001000
| LR_D_01_64A -> Fct7_0001001
| LR_D_10_64A -> Fct7_0001010
| LR_D_11_64A -> Fct7_0001011
| SC_D_00_64A -> Fct7_0001100
| SC_D_01_64A -> Fct7_0001101
| SC_D_10_64A -> Fct7_0001110
| SC_D_11_64A -> Fct7_0001111
| AMOSWAP_D_00_64A -> Fct7_0000100
| AMOSWAP_D_01_64A -> Fct7_0000101
| AMOSWAP_D_10_64A -> Fct7_0000110
| AMOSWAP_D_11_64A -> Fct7_0000111
| AMOADD_D_00_64A -> Fct7_0000000
| AMOADD_D_01_64A -> Fct7_0000001
| AMOADD_D_10_64A -> Fct7_0000010
| AMOADD_D_11_64A -> Fct7_0000011
| AMOXOR_D_00_64A -> Fct7_0010000
| AMOXOR_D_01_64A -> Fct7_0010001
| AMOXOR_D_10_64A -> Fct7_0010010
| AMOXOR_D_11_64A -> Fct7_0010011
| AMOAND_D_00_64A -> Fct7_0110000
| AMOAND_D_01_64A -> Fct7_0110001
| AMOAND_D_10_64A -> Fct7_0110010
| AMOAND_D_11_64A -> Fct7_0110011
| AMOOR_D_00_64A -> Fct7_0100000
| AMOOR_D_01_64A -> Fct7_0100001
| AMOOR_D_10_64A -> Fct7_0100010
| AMOOR_D_11_64A -> Fct7_0100011
| AMOMIN_D_00_64A -> Fct7_1000000
| AMOMIN_D_01_64A -> Fct7_1000001
| AMOMIN_D_10_64A -> Fct7_1000010
| AMOMIN_D_11_64A -> Fct7_1000011
| AMOMAX_D_00_64A -> Fct7_1010000
| AMOMAX_D_01_64A -> Fct7_1010001
| AMOMAX_D_10_64A -> Fct7_1010010
| AMOMAX_D_11_64A -> Fct7_1010011
| AMOMINU_D_00_64A -> Fct7_1100000
| AMOMINU_D_01_64A -> Fct7_1100001
| AMOMINU_D_10_64A -> Fct7_1100010
| AMOMINU_D_11_64A -> Fct7_1100011
| AMOMAXU_D_00_64A -> Fct7_1110000
| AMOMAXU_D_01_64A -> Fct7_1110001
| AMOMAXU_D_10_64A -> Fct7_1110010
| AMOMAXU_D_11_64A -> Fct7_1110011
| FADD_RNE_S_32F -> Fct7_0000000
| FADD_RTZ_S_32F -> Fct7_0000000
| FADD_RDN_S_32F -> Fct7_0000000
| FADD_RUP_S_32F -> Fct7_0000000
| FADD_RMM_S_32F -> Fct7_0000000
| FADD_DYN_S_32F -> Fct7_0000000
| FSUB_RNE_S_32F -> Fct7_0000100
| FSUB_RTZ_S_32F -> Fct7_0000100
| FSUB_RDN_S_32F -> Fct7_0000100
| FSUB_RUP_S_32F -> Fct7_0000100
| FSUB_RMM_S_32F -> Fct7_0000100
| FSUB_DYN_S_32F -> Fct7_0000100
| FMUL_RNE_S_32F -> Fct7_0001000
| FMUL_RTZ_S_32F -> Fct7_0001000
| FMUL_RDN_S_32F -> Fct7_0001000
| FMUL_RUP_S_32F -> Fct7_0001000
| FMUL_RMM_S_32F -> Fct7_0001000
| FMUL_DYN_S_32F -> Fct7_0001000
| FDIV_RNE_S_32F -> Fct7_0001100
| FDIV_RTZ_S_32F -> Fct7_0001100
| FDIV_RDN_S_32F -> Fct7_0001100
| FDIV_RUP_S_32F -> Fct7_0001100
| FDIV_RMM_S_32F -> Fct7_0001100
| FDIV_DYN_S_32F -> Fct7_0001100
| FSQRT_RNE_S_32F -> Fct7_0101100
| FSQRT_RTZ_S_32F -> Fct7_0101100
| FSQRT_RDN_S_32F -> Fct7_0101100
| FSQRT_RUP_S_32F -> Fct7_0101100
| FSQRT_RMM_S_32F -> Fct7_0101100
| FSQRT_DYN_S_32F -> Fct7_0101100
| FSGNJ_S_32F -> Fct7_0010000
| FSGNJN_S_32F -> Fct7_0010000
| FSGNJX_S_32F -> Fct7_0010000
| FMIN_S_32F -> Fct7_0010100
| FMAX_S_32F -> Fct7_0010100
| FCVT_RNE_W_S_32F -> Fct7_1100000
| FCVT_RTZ_W_S_32F -> Fct7_1100000
| FCVT_RDN_W_S_32F -> Fct7_1100000
| FCVT_RUP_W_S_32F -> Fct7_1100000
| FCVT_RMM_W_S_32F -> Fct7_1100000
| FCVT_DYN_W_S_32F -> Fct7_1100000
| FCVT_RNE_WU_S_32F -> Fct7_1100000
| FCVT_RTZ_WU_S_32F -> Fct7_1100000
| FCVT_RDN_WU_S_32F -> Fct7_1100000
| FCVT_RUP_WU_S_32F -> Fct7_1100000
| FCVT_RMM_WU_S_32F -> Fct7_1100000
| FCVT_DYN_WU_S_32F -> Fct7_1100000
| FMV_X_W_32F -> Fct7_1110000
| FEQ_S_32F -> Fct7_1010000
| FLT_S_32F -> Fct7_1010000
| FLE_S_32F -> Fct7_1010000
| FCLASS_S_32F -> Fct7_1110000
| FCVT_RNE_S_W_32F -> Fct7_1101000
| FCVT_RTZ_S_W_32F -> Fct7_1101000
| FCVT_RDN_S_W_32F -> Fct7_1101000
| FCVT_RUP_S_W_32F -> Fct7_1101000
| FCVT_RMM_S_W_32F -> Fct7_1101000
| FCVT_DYN_S_W_32F -> Fct7_1101000
| FCVT_RNE_S_WU_32F -> Fct7_1101000
| FCVT_RTZ_S_WU_32F -> Fct7_1101000
| FCVT_RDN_S_WU_32F -> Fct7_1101000
| FCVT_RUP_S_WU_32F -> Fct7_1101000
| FCVT_RMM_S_WU_32F -> Fct7_1101000
| FCVT_DYN_S_WU_32F -> Fct7_1101000
| FMV_W_X_32F -> Fct7_1111000
| FADD_RNE_S_64F -> Fct7_0000000
| FADD_RTZ_S_64F -> Fct7_0000000
| FADD_RDN_S_64F -> Fct7_0000000
| FADD_RUP_S_64F -> Fct7_0000000
| FADD_RMM_S_64F -> Fct7_0000000
| FADD_DYN_S_64F -> Fct7_0000000
| FSUB_RNE_S_64F -> Fct7_0000100
| FSUB_RTZ_S_64F -> Fct7_0000100
| FSUB_RDN_S_64F -> Fct7_0000100
| FSUB_RUP_S_64F -> Fct7_0000100
| FSUB_RMM_S_64F -> Fct7_0000100
| FSUB_DYN_S_64F -> Fct7_0000100
| FMUL_RNE_S_64F -> Fct7_0001000
| FMUL_RTZ_S_64F -> Fct7_0001000
| FMUL_RDN_S_64F -> Fct7_0001000
| FMUL_RUP_S_64F -> Fct7_0001000
| FMUL_RMM_S_64F -> Fct7_0001000
| FMUL_DYN_S_64F -> Fct7_0001000
| FDIV_RNE_S_64F -> Fct7_0001100
| FDIV_RTZ_S_64F -> Fct7_0001100
| FDIV_RDN_S_64F -> Fct7_0001100
| FDIV_RUP_S_64F -> Fct7_0001100
| FDIV_RMM_S_64F -> Fct7_0001100
| FDIV_DYN_S_64F -> Fct7_0001100
| FSQRT_RNE_S_64F -> Fct7_0101100
| FSQRT_RTZ_S_64F -> Fct7_0101100
| FSQRT_RDN_S_64F -> Fct7_0101100
| FSQRT_RUP_S_64F -> Fct7_0101100
| FSQRT_RMM_S_64F -> Fct7_0101100
| FSQRT_DYN_S_64F -> Fct7_0101100
| FSGNJ_S_64F -> Fct7_0010000
| FSGNJN_S_64F -> Fct7_0010000
| FSGNJX_S_64F -> Fct7_0010000
| FMIN_S_64F -> Fct7_0010100
| FMAX_S_64F -> Fct7_0010100
| FCVT_RNE_W_S_64F -> Fct7_1100000
| FCVT_RTZ_W_S_64F -> Fct7_1100000
| FCVT_RDN_W_S_64F -> Fct7_1100000
| FCVT_RUP_W_S_64F -> Fct7_1100000
| FCVT_RMM_W_S_64F -> Fct7_1100000
| FCVT_DYN_W_S_64F -> Fct7_1100000
| FCVT_RNE_WU_S_64F -> Fct7_1100000
| FCVT_RTZ_WU_S_64F -> Fct7_1100000
| FCVT_RDN_WU_S_64F -> Fct7_1100000
| FCVT_RUP_WU_S_64F -> Fct7_1100000
| FCVT_RMM_WU_S_64F -> Fct7_1100000
| FCVT_DYN_WU_S_64F -> Fct7_1100000
| FMV_X_W_64F -> Fct7_1110000
| FEQ_S_64F -> Fct7_1010000
| FLT_S_64F -> Fct7_1010000
| FLE_S_64F -> Fct7_1010000
| FCLASS_S_64F -> Fct7_1110000
| FCVT_RNE_S_W_64F -> Fct7_1101000
| FCVT_RTZ_S_W_64F -> Fct7_1101000
| FCVT_RDN_S_W_64F -> Fct7_1101000
| FCVT_RUP_S_W_64F -> Fct7_1101000
| FCVT_RMM_S_W_64F -> Fct7_1101000
| FCVT_DYN_S_W_64F -> Fct7_1101000
| FCVT_RNE_S_WU_64F -> Fct7_1101000
| FCVT_RTZ_S_WU_64F -> Fct7_1101000
| FCVT_RDN_S_WU_64F -> Fct7_1101000
| FCVT_RUP_S_WU_64F -> Fct7_1101000
| FCVT_RMM_S_WU_64F -> Fct7_1101000
| FCVT_DYN_S_WU_64F -> Fct7_1101000
| FMV_W_X_64F -> Fct7_1111000
| FCVT_RNE_L_S_64F -> Fct7_1100000
| FCVT_RTZ_L_S_64F -> Fct7_1100000
| FCVT_RDN_L_S_64F -> Fct7_1100000
| FCVT_RUP_L_S_64F -> Fct7_1100000
| FCVT_RMM_L_S_64F -> Fct7_1100000
| FCVT_DYN_L_S_64F -> Fct7_1100000
| FCVT_RNE_LU_S_64F -> Fct7_1100000
| FCVT_RTZ_LU_S_64F -> Fct7_1100000
| FCVT_RDN_LU_S_64F -> Fct7_1100000
| FCVT_RUP_LU_S_64F -> Fct7_1100000
| FCVT_RMM_LU_S_64F -> Fct7_1100000
| FCVT_DYN_LU_S_64F -> Fct7_1100000
| FCVT_RNE_S_L_64F -> Fct7_1101000
| FCVT_RTZ_S_L_64F -> Fct7_1101000
| FCVT_RDN_S_L_64F -> Fct7_1101000
| FCVT_RUP_S_L_64F -> Fct7_1101000
| FCVT_RMM_S_L_64F -> Fct7_1101000
| FCVT_DYN_S_L_64F -> Fct7_1101000
| FCVT_RNE_S_LU_64F -> Fct7_1101000
| FCVT_RTZ_S_LU_64F -> Fct7_1101000
| FCVT_RDN_S_LU_64F -> Fct7_1101000
| FCVT_RUP_S_LU_64F -> Fct7_1101000
| FCVT_RMM_S_LU_64F -> Fct7_1101000
| FCVT_DYN_S_LU_64F -> Fct7_1101000
| FADD_RNE_D_32D -> Fct7_0000001
| FADD_RTZ_D_32D -> Fct7_0000001
| FADD_RDN_D_32D -> Fct7_0000001
| FADD_RUP_D_32D -> Fct7_0000001
| FADD_RMM_D_32D -> Fct7_0000001
| FADD_DYN_D_32D -> Fct7_0000001
| FSUB_RNE_D_32D -> Fct7_0000101
| FSUB_RTZ_D_32D -> Fct7_0000101
| FSUB_RDN_D_32D -> Fct7_0000101
| FSUB_RUP_D_32D -> Fct7_0000101
| FSUB_RMM_D_32D -> Fct7_0000101
| FSUB_DYN_D_32D -> Fct7_0000101
| FMUL_RNE_D_32D -> Fct7_0001001
| FMUL_RTZ_D_32D -> Fct7_0001001
| FMUL_RDN_D_32D -> Fct7_0001001
| FMUL_RUP_D_32D -> Fct7_0001001
| FMUL_RMM_D_32D -> Fct7_0001001
| FMUL_DYN_D_32D -> Fct7_0001001
| FDIV_RNE_D_32D -> Fct7_0001101
| FDIV_RTZ_D_32D -> Fct7_0001101
| FDIV_RDN_D_32D -> Fct7_0001101
| FDIV_RUP_D_32D -> Fct7_0001101
| FDIV_RMM_D_32D -> Fct7_0001101
| FDIV_DYN_D_32D -> Fct7_0001101
| FSQRT_RNE_D_32D -> Fct7_0101101
| FSQRT_RTZ_D_32D -> Fct7_0101101
| FSQRT_RDN_D_32D -> Fct7_0101101
| FSQRT_RUP_D_32D -> Fct7_0101101
| FSQRT_RMM_D_32D -> Fct7_0101101
| FSQRT_DYN_D_32D -> Fct7_0101101
| FSGNJ_D_32D -> Fct7_0010001
| FSGNJN_D_32D -> Fct7_0010001
| FSGNJX_D_32D -> Fct7_0010001
| FMIN_D_32D -> Fct7_0010101
| FMAX_D_32D -> Fct7_0010101
| FCVT_RNE_S_D_32D -> Fct7_0100000
| FCVT_RTZ_S_D_32D -> Fct7_0100000
| FCVT_RDN_S_D_32D -> Fct7_0100000
| FCVT_RUP_S_D_32D -> Fct7_0100000
| FCVT_RMM_S_D_32D -> Fct7_0100000
| FCVT_DYN_S_D_32D -> Fct7_0100000
| FCVT_RNE_D_S_32D -> Fct7_0100001
| FCVT_RTZ_D_S_32D -> Fct7_0100001
| FCVT_RDN_D_S_32D -> Fct7_0100001
| FCVT_RUP_D_S_32D -> Fct7_0100001
| FCVT_RMM_D_S_32D -> Fct7_0100001
| FCVT_DYN_D_S_32D -> Fct7_0100001
| FEQ_D_32D -> Fct7_1010001
| FLT_D_32D -> Fct7_1010001
| FLE_D_32D -> Fct7_1010001
| FCLASS_D_32D -> Fct7_1110001
| FCVT_RNE_W_D_32D -> Fct7_1100001
| FCVT_RTZ_W_D_32D -> Fct7_1100001
| FCVT_RDN_W_D_32D -> Fct7_1100001
| FCVT_RUP_W_D_32D -> Fct7_1100001
| FCVT_RMM_W_D_32D -> Fct7_1100001
| FCVT_DYN_W_D_32D -> Fct7_1100001
| FCVT_RNE_WU_D_32D -> Fct7_1100001
| FCVT_RTZ_WU_D_32D -> Fct7_1100001
| FCVT_RDN_WU_D_32D -> Fct7_1100001
| FCVT_RUP_WU_D_32D -> Fct7_1100001
| FCVT_RMM_WU_D_32D -> Fct7_1100001
| FCVT_DYN_WU_D_32D -> Fct7_1100001
| FCVT_RNE_D_W_32D -> Fct7_1101001
| FCVT_RTZ_D_W_32D -> Fct7_1101001
| FCVT_RDN_D_W_32D -> Fct7_1101001
| FCVT_RUP_D_W_32D -> Fct7_1101001
| FCVT_RMM_D_W_32D -> Fct7_1101001
| FCVT_DYN_D_W_32D -> Fct7_1101001
| FCVT_RNE_D_WU_32D -> Fct7_1101001
| FCVT_RTZ_D_WU_32D -> Fct7_1101001
| FCVT_RDN_D_WU_32D -> Fct7_1101001
| FCVT_RUP_D_WU_32D -> Fct7_1101001
| FCVT_RMM_D_WU_32D -> Fct7_1101001
| FCVT_DYN_D_WU_32D -> Fct7_1101001
| FADD_RNE_D_64D -> Fct7_0000001
| FADD_RTZ_D_64D -> Fct7_0000001
| FADD_RDN_D_64D -> Fct7_0000001
| FADD_RUP_D_64D -> Fct7_0000001
| FADD_RMM_D_64D -> Fct7_0000001
| FADD_DYN_D_64D -> Fct7_0000001
| FSUB_RNE_D_64D -> Fct7_0000101
| FSUB_RTZ_D_64D -> Fct7_0000101
| FSUB_RDN_D_64D -> Fct7_0000101
| FSUB_RUP_D_64D -> Fct7_0000101
| FSUB_RMM_D_64D -> Fct7_0000101
| FSUB_DYN_D_64D -> Fct7_0000101
| FMUL_RNE_D_64D -> Fct7_0001001
| FMUL_RTZ_D_64D -> Fct7_0001001
| FMUL_RDN_D_64D -> Fct7_0001001
| FMUL_RUP_D_64D -> Fct7_0001001
| FMUL_RMM_D_64D -> Fct7_0001001
| FMUL_DYN_D_64D -> Fct7_0001001
| FDIV_RNE_D_64D -> Fct7_0001101
| FDIV_RTZ_D_64D -> Fct7_0001101
| FDIV_RDN_D_64D -> Fct7_0001101
| FDIV_RUP_D_64D -> Fct7_0001101
| FDIV_RMM_D_64D -> Fct7_0001101
| FDIV_DYN_D_64D -> Fct7_0001101
| FSQRT_RNE_D_64D -> Fct7_0101101
| FSQRT_RTZ_D_64D -> Fct7_0101101
| FSQRT_RDN_D_64D -> Fct7_0101101
| FSQRT_RUP_D_64D -> Fct7_0101101
| FSQRT_RMM_D_64D -> Fct7_0101101
| FSQRT_DYN_D_64D -> Fct7_0101101
| FSGNJ_D_64D -> Fct7_0010001
| FSGNJN_D_64D -> Fct7_0010001
| FSGNJX_D_64D -> Fct7_0010001
| FMIN_D_64D -> Fct7_0010101
| FMAX_D_64D -> Fct7_0010101
| FCVT_RNE_S_D_64D -> Fct7_0100000
| FCVT_RTZ_S_D_64D -> Fct7_0100000
| FCVT_RDN_S_D_64D -> Fct7_0100000
| FCVT_RUP_S_D_64D -> Fct7_0100000
| FCVT_RMM_S_D_64D -> Fct7_0100000
| FCVT_DYN_S_D_64D -> Fct7_0100000
| FCVT_RNE_D_S_64D -> Fct7_0100001
| FCVT_RTZ_D_S_64D -> Fct7_0100001
| FCVT_RDN_D_S_64D -> Fct7_0100001
| FCVT_RUP_D_S_64D -> Fct7_0100001
| FCVT_RMM_D_S_64D -> Fct7_0100001
| FCVT_DYN_D_S_64D -> Fct7_0100001
| FEQ_D_64D -> Fct7_1010001
| FLT_D_64D -> Fct7_1010001
| FLE_D_64D -> Fct7_1010001
| FCLASS_D_64D -> Fct7_1110001
| FCVT_RNE_W_D_64D -> Fct7_1100001
| FCVT_RTZ_W_D_64D -> Fct7_1100001
| FCVT_RDN_W_D_64D -> Fct7_1100001
| FCVT_RUP_W_D_64D -> Fct7_1100001
| FCVT_RMM_W_D_64D -> Fct7_1100001
| FCVT_DYN_W_D_64D -> Fct7_1100001
| FCVT_RNE_WU_D_64D -> Fct7_1100001
| FCVT_RTZ_WU_D_64D -> Fct7_1100001
| FCVT_RDN_WU_D_64D -> Fct7_1100001
| FCVT_RUP_WU_D_64D -> Fct7_1100001
| FCVT_RMM_WU_D_64D -> Fct7_1100001
| FCVT_DYN_WU_D_64D -> Fct7_1100001
| FCVT_RNE_D_W_64D -> Fct7_1101001
| FCVT_RTZ_D_W_64D -> Fct7_1101001
| FCVT_RDN_D_W_64D -> Fct7_1101001
| FCVT_RUP_D_W_64D -> Fct7_1101001
| FCVT_RMM_D_W_64D -> Fct7_1101001
| FCVT_DYN_D_W_64D -> Fct7_1101001
| FCVT_RNE_D_WU_64D -> Fct7_1101001
| FCVT_RTZ_D_WU_64D -> Fct7_1101001
| FCVT_RDN_D_WU_64D -> Fct7_1101001
| FCVT_RUP_D_WU_64D -> Fct7_1101001
| FCVT_RMM_D_WU_64D -> Fct7_1101001
| FCVT_DYN_D_WU_64D -> Fct7_1101001
| FCVT_RNE_L_D_64D -> Fct7_1100001
| FCVT_RTZ_L_D_64D -> Fct7_1100001
| FCVT_RDN_L_D_64D -> Fct7_1100001
| FCVT_RUP_L_D_64D -> Fct7_1100001
| FCVT_RMM_L_D_64D -> Fct7_1100001
| FCVT_DYN_L_D_64D -> Fct7_1100001
| FCVT_RNE_LU_D_64D -> Fct7_1100001
| FCVT_RTZ_LU_D_64D -> Fct7_1100001
| FCVT_RDN_LU_D_64D -> Fct7_1100001
| FCVT_RUP_LU_D_64D -> Fct7_1100001
| FCVT_RMM_LU_D_64D -> Fct7_1100001
| FCVT_DYN_LU_D_64D -> Fct7_1100001
| FMV_X_D_64D -> Fct7_1110001
| FCVT_RNE_D_L_64D -> Fct7_1101001
| FCVT_RTZ_D_L_64D -> Fct7_1101001
| FCVT_RDN_D_L_64D -> Fct7_1101001
| FCVT_RUP_D_L_64D -> Fct7_1101001
| FCVT_RMM_D_L_64D -> Fct7_1101001
| FCVT_DYN_D_L_64D -> Fct7_1101001
| FCVT_RNE_D_LU_64D -> Fct7_1101001
| FCVT_RTZ_D_LU_64D -> Fct7_1101001
| FCVT_RDN_D_LU_64D -> Fct7_1101001
| FCVT_RUP_D_LU_64D -> Fct7_1101001
| FCVT_RMM_D_LU_64D -> Fct7_1101001
| FCVT_DYN_D_LU_64D -> Fct7_1101001
| FMV_D_X_64D -> Fct7_1111001
| FADD_RNE_Q_32Q -> Fct7_0000011
| FADD_RTZ_Q_32Q -> Fct7_0000011
| FADD_RDN_Q_32Q -> Fct7_0000011
| FADD_RUP_Q_32Q -> Fct7_0000011
| FADD_RMM_Q_32Q -> Fct7_0000011
| FADD_DYN_Q_32Q -> Fct7_0000011
| FSUB_RNE_Q_32Q -> Fct7_0000111
| FSUB_RTZ_Q_32Q -> Fct7_0000111
| FSUB_RDN_Q_32Q -> Fct7_0000111
| FSUB_RUP_Q_32Q -> Fct7_0000111
| FSUB_RMM_Q_32Q -> Fct7_0000111
| FSUB_DYN_Q_32Q -> Fct7_0000111
| FMUL_RNE_Q_32Q -> Fct7_0001011
| FMUL_RTZ_Q_32Q -> Fct7_0001011
| FMUL_RDN_Q_32Q -> Fct7_0001011
| FMUL_RUP_Q_32Q -> Fct7_0001011
| FMUL_RMM_Q_32Q -> Fct7_0001011
| FMUL_DYN_Q_32Q -> Fct7_0001011
| FDIV_RNE_Q_32Q -> Fct7_0001111
| FDIV_RTZ_Q_32Q -> Fct7_0001111
| FDIV_RDN_Q_32Q -> Fct7_0001111
| FDIV_RUP_Q_32Q -> Fct7_0001111
| FDIV_RMM_Q_32Q -> Fct7_0001111
| FDIV_DYN_Q_32Q -> Fct7_0001111
| FSQRT_RNE_Q_32Q -> Fct7_0101111
| FSQRT_RTZ_Q_32Q -> Fct7_0101111
| FSQRT_RDN_Q_32Q -> Fct7_0101111
| FSQRT_RUP_Q_32Q -> Fct7_0101111
| FSQRT_RMM_Q_32Q -> Fct7_0101111
| FSQRT_DYN_Q_32Q -> Fct7_0101111
| FSGNJ_Q_32Q -> Fct7_0010011
| FSGNJN_Q_32Q -> Fct7_0010011
| FSGNJX_Q_32Q -> Fct7_0010011
| FMIN_Q_32Q -> Fct7_0010111
| FMAX_Q_32Q -> Fct7_0010111
| FCVT_RNE_S_Q_32Q -> Fct7_0100000
| FCVT_RTZ_S_Q_32Q -> Fct7_0100000
| FCVT_RDN_S_Q_32Q -> Fct7_0100000
| FCVT_RUP_S_Q_32Q -> Fct7_0100000
| FCVT_RMM_S_Q_32Q -> Fct7_0100000
| FCVT_DYN_S_Q_32Q -> Fct7_0100000
| FCVT_RNE_Q_S_32Q -> Fct7_0100011
| FCVT_RTZ_Q_S_32Q -> Fct7_0100011
| FCVT_RDN_Q_S_32Q -> Fct7_0100011
| FCVT_RUP_Q_S_32Q -> Fct7_0100011
| FCVT_RMM_Q_S_32Q -> Fct7_0100011
| FCVT_DYN_Q_S_32Q -> Fct7_0100011
| FCVT_RNE_D_Q_32Q -> Fct7_0100001
| FCVT_RTZ_D_Q_32Q -> Fct7_0100001
| FCVT_RDN_D_Q_32Q -> Fct7_0100001
| FCVT_RUP_D_Q_32Q -> Fct7_0100001
| FCVT_RMM_D_Q_32Q -> Fct7_0100001
| FCVT_DYN_D_Q_32Q -> Fct7_0100001
| FCVT_RNE_Q_D_32Q -> Fct7_0100011
| FCVT_RTZ_Q_D_32Q -> Fct7_0100011
| FCVT_RDN_Q_D_32Q -> Fct7_0100011
| FCVT_RUP_Q_D_32Q -> Fct7_0100011
| FCVT_RMM_Q_D_32Q -> Fct7_0100011
| FCVT_DYN_Q_D_32Q -> Fct7_0100011
| FEQ_Q_32Q -> Fct7_1010011
| FLT_Q_32Q -> Fct7_1010011
| FLE_Q_32Q -> Fct7_1010011
| FCLASS_Q_32Q -> Fct7_1110011
| FCVT_RNE_W_Q_32Q -> Fct7_1100011
| FCVT_RTZ_W_Q_32Q -> Fct7_1100011
| FCVT_RDN_W_Q_32Q -> Fct7_1100011
| FCVT_RUP_W_Q_32Q -> Fct7_1100011
| FCVT_RMM_W_Q_32Q -> Fct7_1100011
| FCVT_DYN_W_Q_32Q -> Fct7_1100011
| FCVT_RNE_WU_Q_32Q -> Fct7_1100011
| FCVT_RTZ_WU_Q_32Q -> Fct7_1100011
| FCVT_RDN_WU_Q_32Q -> Fct7_1100011
| FCVT_RUP_WU_Q_32Q -> Fct7_1100011
| FCVT_RMM_WU_Q_32Q -> Fct7_1100011
| FCVT_DYN_WU_Q_32Q -> Fct7_1100011
| FCVT_RNE_Q_W_32Q -> Fct7_1101011
| FCVT_RTZ_Q_W_32Q -> Fct7_1101011
| FCVT_RDN_Q_W_32Q -> Fct7_1101011
| FCVT_RUP_Q_W_32Q -> Fct7_1101011
| FCVT_RMM_Q_W_32Q -> Fct7_1101011
| FCVT_DYN_Q_W_32Q -> Fct7_1101011
| FCVT_RNE_Q_WU_32Q -> Fct7_1101011
| FCVT_RTZ_Q_WU_32Q -> Fct7_1101011
| FCVT_RDN_Q_WU_32Q -> Fct7_1101011
| FCVT_RUP_Q_WU_32Q -> Fct7_1101011
| FCVT_RMM_Q_WU_32Q -> Fct7_1101011
| FCVT_DYN_Q_WU_32Q -> Fct7_1101011
| FADD_RNE_Q_64Q -> Fct7_0000011
| FADD_RTZ_Q_64Q -> Fct7_0000011
| FADD_RDN_Q_64Q -> Fct7_0000011
| FADD_RUP_Q_64Q -> Fct7_0000011
| FADD_RMM_Q_64Q -> Fct7_0000011
| FADD_DYN_Q_64Q -> Fct7_0000011
| FSUB_RNE_Q_64Q -> Fct7_0000111
| FSUB_RTZ_Q_64Q -> Fct7_0000111
| FSUB_RDN_Q_64Q -> Fct7_0000111
| FSUB_RUP_Q_64Q -> Fct7_0000111
| FSUB_RMM_Q_64Q -> Fct7_0000111
| FSUB_DYN_Q_64Q -> Fct7_0000111
| FMUL_RNE_Q_64Q -> Fct7_0001011
| FMUL_RTZ_Q_64Q -> Fct7_0001011
| FMUL_RDN_Q_64Q -> Fct7_0001011
| FMUL_RUP_Q_64Q -> Fct7_0001011
| FMUL_RMM_Q_64Q -> Fct7_0001011
| FMUL_DYN_Q_64Q -> Fct7_0001011
| FDIV_RNE_Q_64Q -> Fct7_0001111
| FDIV_RTZ_Q_64Q -> Fct7_0001111
| FDIV_RDN_Q_64Q -> Fct7_0001111
| FDIV_RUP_Q_64Q -> Fct7_0001111
| FDIV_RMM_Q_64Q -> Fct7_0001111
| FDIV_DYN_Q_64Q -> Fct7_0001111
| FSQRT_RNE_Q_64Q -> Fct7_0101111
| FSQRT_RTZ_Q_64Q -> Fct7_0101111
| FSQRT_RDN_Q_64Q -> Fct7_0101111
| FSQRT_RUP_Q_64Q -> Fct7_0101111
| FSQRT_RMM_Q_64Q -> Fct7_0101111
| FSQRT_DYN_Q_64Q -> Fct7_0101111
| FSGNJ_Q_64Q -> Fct7_0010011
| FSGNJN_Q_64Q -> Fct7_0010011
| FSGNJX_Q_64Q -> Fct7_0010011
| FMIN_Q_64Q -> Fct7_0010111
| FMAX_Q_64Q -> Fct7_0010111
| FCVT_RNE_S_Q_64Q -> Fct7_0100000
| FCVT_RTZ_S_Q_64Q -> Fct7_0100000
| FCVT_RDN_S_Q_64Q -> Fct7_0100000
| FCVT_RUP_S_Q_64Q -> Fct7_0100000
| FCVT_RMM_S_Q_64Q -> Fct7_0100000
| FCVT_DYN_S_Q_64Q -> Fct7_0100000
| FCVT_RNE_Q_S_64Q -> Fct7_0100011
| FCVT_RTZ_Q_S_64Q -> Fct7_0100011
| FCVT_RDN_Q_S_64Q -> Fct7_0100011
| FCVT_RUP_Q_S_64Q -> Fct7_0100011
| FCVT_RMM_Q_S_64Q -> Fct7_0100011
| FCVT_DYN_Q_S_64Q -> Fct7_0100011
| FCVT_RNE_D_Q_64Q -> Fct7_0100001
| FCVT_RTZ_D_Q_64Q -> Fct7_0100001
| FCVT_RDN_D_Q_64Q -> Fct7_0100001
| FCVT_RUP_D_Q_64Q -> Fct7_0100001
| FCVT_RMM_D_Q_64Q -> Fct7_0100001
| FCVT_DYN_D_Q_64Q -> Fct7_0100001
| FCVT_RNE_Q_D_64Q -> Fct7_0100011
| FCVT_RTZ_Q_D_64Q -> Fct7_0100011
| FCVT_RDN_Q_D_64Q -> Fct7_0100011
| FCVT_RUP_Q_D_64Q -> Fct7_0100011
| FCVT_RMM_Q_D_64Q -> Fct7_0100011
| FCVT_DYN_Q_D_64Q -> Fct7_0100011
| FEQ_Q_64Q -> Fct7_1010011
| FLT_Q_64Q -> Fct7_1010011
| FLE_Q_64Q -> Fct7_1010011
| FCLASS_Q_64Q -> Fct7_1110011
| FCVT_RNE_W_Q_64Q -> Fct7_1100011
| FCVT_RTZ_W_Q_64Q -> Fct7_1100011
| FCVT_RDN_W_Q_64Q -> Fct7_1100011
| FCVT_RUP_W_Q_64Q -> Fct7_1100011
| FCVT_RMM_W_Q_64Q -> Fct7_1100011
| FCVT_DYN_W_Q_64Q -> Fct7_1100011
| FCVT_RNE_WU_Q_64Q -> Fct7_1100011
| FCVT_RTZ_WU_Q_64Q -> Fct7_1100011
| FCVT_RDN_WU_Q_64Q -> Fct7_1100011
| FCVT_RUP_WU_Q_64Q -> Fct7_1100011
| FCVT_RMM_WU_Q_64Q -> Fct7_1100011
| FCVT_DYN_WU_Q_64Q -> Fct7_1100011
| FCVT_RNE_Q_W_64Q -> Fct7_1101011
| FCVT_RTZ_Q_W_64Q -> Fct7_1101011
| FCVT_RDN_Q_W_64Q -> Fct7_1101011
| FCVT_RUP_Q_W_64Q -> Fct7_1101011
| FCVT_RMM_Q_W_64Q -> Fct7_1101011
| FCVT_DYN_Q_W_64Q -> Fct7_1101011
| FCVT_RNE_Q_WU_64Q -> Fct7_1101011
| FCVT_RTZ_Q_WU_64Q -> Fct7_1101011
| FCVT_RDN_Q_WU_64Q -> Fct7_1101011
| FCVT_RUP_Q_WU_64Q -> Fct7_1101011
| FCVT_RMM_Q_WU_64Q -> Fct7_1101011
| FCVT_DYN_Q_WU_64Q -> Fct7_1101011
| FCVT_RNE_L_Q_64Q -> Fct7_1100011
| FCVT_RTZ_L_Q_64Q -> Fct7_1100011
| FCVT_RDN_L_Q_64Q -> Fct7_1100011
| FCVT_RUP_L_Q_64Q -> Fct7_1100011
| FCVT_RMM_L_Q_64Q -> Fct7_1100011
| FCVT_DYN_L_Q_64Q -> Fct7_1100011
| FCVT_RNE_LU_Q_64Q -> Fct7_1100011
| FCVT_RTZ_LU_Q_64Q -> Fct7_1100011
| FCVT_RDN_LU_Q_64Q -> Fct7_1100011
| FCVT_RUP_LU_Q_64Q -> Fct7_1100011
| FCVT_RMM_LU_Q_64Q -> Fct7_1100011
| FCVT_DYN_LU_Q_64Q -> Fct7_1100011
| FCVT_RNE_Q_L_64Q -> Fct7_1101011
| FCVT_RTZ_Q_L_64Q -> Fct7_1101011
| FCVT_RDN_Q_L_64Q -> Fct7_1101011
| FCVT_RUP_Q_L_64Q -> Fct7_1101011
| FCVT_RMM_Q_L_64Q -> Fct7_1101011
| FCVT_DYN_Q_L_64Q -> Fct7_1101011
| FCVT_RNE_Q_LU_64Q -> Fct7_1101011
| FCVT_RTZ_Q_LU_64Q -> Fct7_1101011
| FCVT_RDN_Q_LU_64Q -> Fct7_1101011
| FCVT_RUP_Q_LU_64Q -> Fct7_1101011
| FCVT_RMM_Q_LU_64Q -> Fct7_1101011
| FCVT_DYN_Q_LU_64Q -> Fct7_1101011
| _ -> assert false (* absurd case *)

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

(** val get_present_i_types_from_instructions :
    instruction list -> present_i_types **)

let get_present_i_types_from_instructions instructions0 =
  let all_absent = { rType_present = false; r4Type_present = false;
    iType_present = false; sType_present = false; bType_present = false;
    uType_present = false; jType_present = false }
  in
  fold_left (fun p i ->
    match get_instruction_i_type i with
    | RType ->
      { rType_present = true; r4Type_present = p.r4Type_present;
        iType_present = p.iType_present; sType_present = p.sType_present;
        bType_present = p.bType_present; uType_present = p.uType_present;
        jType_present = p.jType_present }
    | R4Type ->
      { rType_present = p.rType_present; r4Type_present = true;
        iType_present = p.iType_present; sType_present = p.sType_present;
        bType_present = p.bType_present; uType_present = p.uType_present;
        jType_present = p.jType_present }
    | IType ->
      { rType_present = p.rType_present; r4Type_present = p.r4Type_present;
        iType_present = true; sType_present = p.sType_present;
        bType_present = p.bType_present; uType_present = p.uType_present;
        jType_present = p.jType_present }
    | SType ->
      { rType_present = p.rType_present; r4Type_present = p.r4Type_present;
        iType_present = p.iType_present; sType_present = true;
        bType_present = p.bType_present; uType_present = p.uType_present;
        jType_present = p.jType_present }
    | BType ->
      { rType_present = p.rType_present; r4Type_present = p.r4Type_present;
        iType_present = p.iType_present; sType_present = p.sType_present;
        bType_present = true; uType_present = p.uType_present;
        jType_present = p.jType_present }
    | UType ->
      { rType_present = p.rType_present; r4Type_present = p.r4Type_present;
        iType_present = p.iType_present; sType_present = p.sType_present;
        bType_present = p.bType_present; uType_present = true;
        jType_present = p.jType_present }
    | JType ->
      { rType_present = p.rType_present; r4Type_present = p.r4Type_present;
        iType_present = p.iType_present; sType_present = p.sType_present;
        bType_present = p.bType_present; uType_present = p.uType_present;
        jType_present = true }) instructions0 all_absent

(** val check_i_type_presence : present_i_types -> i_type -> i_type option **)

let check_i_type_presence present_types t = match t with
| RType -> if present_types.rType_present then Some t else None
| R4Type -> if present_types.r4Type_present then Some t else None
| IType -> if present_types.iType_present then Some t else None
| SType -> if present_types.sType_present then Some t else None
| BType -> if present_types.bType_present then Some t else None
| UType -> if present_types.uType_present then Some t else None
| JType -> if present_types.jType_present then Some t else None

(** val get_i_types_from_present_i_types : present_i_types -> i_type list **)

let get_i_types_from_present_i_types present_types =
  let all_types =
    RType :: (R4Type :: (IType :: (SType :: (BType :: (UType :: (JType :: []))))))
  in
  let after = map (check_i_type_presence present_types) all_types in
  fold_left (fun p t -> match t with
                        | Some x -> x :: p
                        | None -> p) after []

(** val get_present_i_fields_from_i_type : i_type -> present_i_fields **)

let get_present_i_fields_from_i_type type1 =
  { opcode_present = (has_opcode type1); fct2_present = (has_fct2 type1);
    fct3_present = (has_fct3 type1); fct7_present = (has_fct7 type1);
    rs1_present = (has_rs1 type1); rs2_present = (has_rs2 type1);
    rs3_present = (has_rs3 type1); rd_present = (has_rd type1);
    immI_present = (has_immI type1); immS_present = (has_immS type1);
    immB_present = (has_immB type1); immU_present = (has_immU type1);
    immJ_present = (has_immJ type1) }

(** val merge_present_i_fields :
    present_i_fields -> present_i_fields -> present_i_fields **)

let merge_present_i_fields fp1 fp2 =
  { opcode_present = ((||) fp1.opcode_present fp2.opcode_present);
    fct2_present = ((||) fp1.fct2_present fp2.fct2_present); fct3_present =
    ((||) fp1.fct3_present fp2.fct3_present); fct7_present =
    ((||) fp1.fct7_present fp2.fct7_present); rs1_present =
    ((||) fp1.rs1_present fp2.rs1_present); rs2_present =
    ((||) fp1.rs2_present fp2.rs2_present); rs3_present =
    ((||) fp1.rs3_present fp2.rs3_present); rd_present =
    ((||) fp1.rd_present fp2.rd_present); immI_present =
    ((||) fp1.immI_present fp2.immI_present); immS_present =
    ((||) fp1.immS_present fp2.immS_present); immB_present =
    ((||) fp1.immB_present fp2.immB_present); immU_present =
    ((||) fp1.immU_present fp2.immU_present); immJ_present =
    ((||) fp1.immJ_present fp2.immJ_present) }

(** val get_present_i_fields_from_i_types :
    i_type list -> present_i_fields **)

let get_present_i_fields_from_i_types types =
  let no_i_fields = { opcode_present = false; fct2_present = false;
    fct3_present = false; fct7_present = false; rs1_present = false;
    rs2_present = false; rs3_present = false; rd_present = false;
    immI_present = false; immS_present = false; immB_present = false;
    immU_present = false; immJ_present = false }
  in
  fold_left (fun p t ->
    merge_present_i_fields p (get_present_i_fields_from_i_type t)) types
    no_i_fields

(** val check_i_field_presence :
    present_i_fields -> i_field -> i_field option **)

let check_i_field_presence present_fields f = match f with
| Opcode -> if present_fields.opcode_present then Some f else None
| Fct2 -> if present_fields.fct2_present then Some f else None
| Fct3 -> if present_fields.fct3_present then Some f else None
| Fct7 -> if present_fields.fct7_present then Some f else None
| Rs1 -> if present_fields.rs1_present then Some f else None
| Rs2 -> if present_fields.rs2_present then Some f else None
| Rs3 -> if present_fields.rs3_present then Some f else None
| Rd -> if present_fields.rd_present then Some f else None
| ImmI -> if present_fields.immI_present then Some f else None
| ImmS -> if present_fields.immS_present then Some f else None
| ImmB -> if present_fields.immB_present then Some f else None
| ImmU -> if present_fields.immU_present then Some f else None
| ImmJ -> if present_fields.immJ_present then Some f else None

(** val get_i_fields_list_from_present_i_fields :
    present_i_fields -> i_field list **)

let get_i_fields_list_from_present_i_fields present_fields =
  let all_i_fields =
    Opcode :: (Fct2 :: (Fct3 :: (Fct7 :: (Rs1 :: (Rs2 :: (Rs3 :: (Rd :: (ImmI :: (ImmS :: (ImmB :: (ImmU :: (ImmJ :: []))))))))))))
  in
  let after = map (check_i_field_presence present_fields) all_i_fields in
  fold_left (fun p f -> match f with
                        | Some f0 -> f0 :: p
                        | None -> p) after []

(** val get_i_fields_list_from_instructions :
    instruction list -> i_field list **)

let get_i_fields_list_from_instructions instrs =
  get_i_fields_list_from_present_i_fields
    (get_present_i_fields_from_i_types
      (get_i_types_from_present_i_types
        (get_present_i_types_from_instructions instrs)))

(** val get_present_opcodes_from_instructions :
    instruction list -> present_opcodes **)

let get_present_opcodes_from_instructions instrs =
  let all_absent = { opc_OP_present = false; opc_JALR_present = false;
    opc_LOAD_present = false; opc_OP_IMM_present = false;
    opc_MISC_MEM_present = false; opc_STORE_present = false;
    opc_BRANCH_present = false; opc_LUI_present = false; opc_AUIPC_present =
    false; opc_JAL_present = false; opc_SYSTEM_present = false;
    opc_OP_32_present = false; opc_OP_IMM_32_present = false;
    opc_AMO_present = false; opc_OP_FP_present = false; opc_MADD_present =
    false; opc_MSUB_present = false; opc_NMSUB_present = false;
    opc_NMADD_present = false; opc_LOAD_FP_present = false;
    opc_STORE_FP_present = false }
  in
  fold_left (fun p i ->
    match instruction_opcode i with
    | Opc_OP ->
      { opc_OP_present = true; opc_JALR_present = p.opc_JALR_present;
        opc_LOAD_present = p.opc_LOAD_present; opc_OP_IMM_present =
        p.opc_OP_IMM_present; opc_MISC_MEM_present = p.opc_MISC_MEM_present;
        opc_STORE_present = p.opc_STORE_present; opc_BRANCH_present =
        p.opc_BRANCH_present; opc_LUI_present = p.opc_LUI_present;
        opc_AUIPC_present = p.opc_AUIPC_present; opc_JAL_present =
        p.opc_JAL_present; opc_SYSTEM_present = p.opc_SYSTEM_present;
        opc_OP_32_present = p.opc_OP_32_present; opc_OP_IMM_32_present =
        p.opc_OP_IMM_32_present; opc_AMO_present = p.opc_AMO_present;
        opc_OP_FP_present = p.opc_OP_FP_present; opc_MADD_present =
        p.opc_MADD_present; opc_MSUB_present = p.opc_MSUB_present;
        opc_NMSUB_present = p.opc_NMSUB_present; opc_NMADD_present =
        p.opc_NMADD_present; opc_LOAD_FP_present = p.opc_LOAD_FP_present;
        opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_JALR ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present = true;
        opc_LOAD_present = p.opc_LOAD_present; opc_OP_IMM_present =
        p.opc_OP_IMM_present; opc_MISC_MEM_present = p.opc_MISC_MEM_present;
        opc_STORE_present = p.opc_STORE_present; opc_BRANCH_present =
        p.opc_BRANCH_present; opc_LUI_present = p.opc_LUI_present;
        opc_AUIPC_present = p.opc_AUIPC_present; opc_JAL_present =
        p.opc_JAL_present; opc_SYSTEM_present = p.opc_SYSTEM_present;
        opc_OP_32_present = p.opc_OP_32_present; opc_OP_IMM_32_present =
        p.opc_OP_IMM_32_present; opc_AMO_present = p.opc_AMO_present;
        opc_OP_FP_present = p.opc_OP_FP_present; opc_MADD_present =
        p.opc_MADD_present; opc_MSUB_present = p.opc_MSUB_present;
        opc_NMSUB_present = p.opc_NMSUB_present; opc_NMADD_present =
        p.opc_NMADD_present; opc_LOAD_FP_present = p.opc_LOAD_FP_present;
        opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_LOAD ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present =
        p.opc_JALR_present; opc_LOAD_present = true; opc_OP_IMM_present =
        p.opc_OP_IMM_present; opc_MISC_MEM_present = p.opc_MISC_MEM_present;
        opc_STORE_present = p.opc_STORE_present; opc_BRANCH_present =
        p.opc_BRANCH_present; opc_LUI_present = p.opc_LUI_present;
        opc_AUIPC_present = p.opc_AUIPC_present; opc_JAL_present =
        p.opc_JAL_present; opc_SYSTEM_present = p.opc_SYSTEM_present;
        opc_OP_32_present = p.opc_OP_32_present; opc_OP_IMM_32_present =
        p.opc_OP_IMM_32_present; opc_AMO_present = p.opc_AMO_present;
        opc_OP_FP_present = p.opc_OP_FP_present; opc_MADD_present =
        p.opc_MADD_present; opc_MSUB_present = p.opc_MSUB_present;
        opc_NMSUB_present = p.opc_NMSUB_present; opc_NMADD_present =
        p.opc_NMADD_present; opc_LOAD_FP_present = p.opc_LOAD_FP_present;
        opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_OP_IMM ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present =
        p.opc_JALR_present; opc_LOAD_present = p.opc_LOAD_present;
        opc_OP_IMM_present = true; opc_MISC_MEM_present =
        p.opc_MISC_MEM_present; opc_STORE_present = p.opc_STORE_present;
        opc_BRANCH_present = p.opc_BRANCH_present; opc_LUI_present =
        p.opc_LUI_present; opc_AUIPC_present = p.opc_AUIPC_present;
        opc_JAL_present = p.opc_JAL_present; opc_SYSTEM_present =
        p.opc_SYSTEM_present; opc_OP_32_present = p.opc_OP_32_present;
        opc_OP_IMM_32_present = p.opc_OP_IMM_32_present; opc_AMO_present =
        p.opc_AMO_present; opc_OP_FP_present = p.opc_OP_FP_present;
        opc_MADD_present = p.opc_MADD_present; opc_MSUB_present =
        p.opc_MSUB_present; opc_NMSUB_present = p.opc_NMSUB_present;
        opc_NMADD_present = p.opc_NMADD_present; opc_LOAD_FP_present =
        p.opc_LOAD_FP_present; opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_MISC_MEM ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present =
        p.opc_JALR_present; opc_LOAD_present = p.opc_LOAD_present;
        opc_OP_IMM_present = p.opc_OP_IMM_present; opc_MISC_MEM_present =
        true; opc_STORE_present = p.opc_STORE_present; opc_BRANCH_present =
        p.opc_BRANCH_present; opc_LUI_present = p.opc_LUI_present;
        opc_AUIPC_present = p.opc_AUIPC_present; opc_JAL_present =
        p.opc_JAL_present; opc_SYSTEM_present = p.opc_SYSTEM_present;
        opc_OP_32_present = p.opc_OP_32_present; opc_OP_IMM_32_present =
        p.opc_OP_IMM_32_present; opc_AMO_present = p.opc_AMO_present;
        opc_OP_FP_present = p.opc_OP_FP_present; opc_MADD_present =
        p.opc_MADD_present; opc_MSUB_present = p.opc_MSUB_present;
        opc_NMSUB_present = p.opc_NMSUB_present; opc_NMADD_present =
        p.opc_NMADD_present; opc_LOAD_FP_present = p.opc_LOAD_FP_present;
        opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_STORE ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present =
        p.opc_JALR_present; opc_LOAD_present = p.opc_LOAD_present;
        opc_OP_IMM_present = p.opc_OP_IMM_present; opc_MISC_MEM_present =
        p.opc_MISC_MEM_present; opc_STORE_present = true;
        opc_BRANCH_present = p.opc_BRANCH_present; opc_LUI_present =
        p.opc_LUI_present; opc_AUIPC_present = p.opc_AUIPC_present;
        opc_JAL_present = p.opc_JAL_present; opc_SYSTEM_present =
        p.opc_SYSTEM_present; opc_OP_32_present = p.opc_OP_32_present;
        opc_OP_IMM_32_present = p.opc_OP_IMM_32_present; opc_AMO_present =
        p.opc_AMO_present; opc_OP_FP_present = p.opc_OP_FP_present;
        opc_MADD_present = p.opc_MADD_present; opc_MSUB_present =
        p.opc_MSUB_present; opc_NMSUB_present = p.opc_NMSUB_present;
        opc_NMADD_present = p.opc_NMADD_present; opc_LOAD_FP_present =
        p.opc_LOAD_FP_present; opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_BRANCH ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present =
        p.opc_JALR_present; opc_LOAD_present = p.opc_LOAD_present;
        opc_OP_IMM_present = p.opc_OP_IMM_present; opc_MISC_MEM_present =
        p.opc_MISC_MEM_present; opc_STORE_present = p.opc_STORE_present;
        opc_BRANCH_present = true; opc_LUI_present = p.opc_LUI_present;
        opc_AUIPC_present = p.opc_AUIPC_present; opc_JAL_present =
        p.opc_JAL_present; opc_SYSTEM_present = p.opc_SYSTEM_present;
        opc_OP_32_present = p.opc_OP_32_present; opc_OP_IMM_32_present =
        p.opc_OP_IMM_32_present; opc_AMO_present = p.opc_AMO_present;
        opc_OP_FP_present = p.opc_OP_FP_present; opc_MADD_present =
        p.opc_MADD_present; opc_MSUB_present = p.opc_MSUB_present;
        opc_NMSUB_present = p.opc_NMSUB_present; opc_NMADD_present =
        p.opc_NMADD_present; opc_LOAD_FP_present = p.opc_LOAD_FP_present;
        opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_LUI ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present =
        p.opc_JALR_present; opc_LOAD_present = p.opc_LOAD_present;
        opc_OP_IMM_present = p.opc_OP_IMM_present; opc_MISC_MEM_present =
        p.opc_MISC_MEM_present; opc_STORE_present = p.opc_STORE_present;
        opc_BRANCH_present = p.opc_BRANCH_present; opc_LUI_present = true;
        opc_AUIPC_present = p.opc_AUIPC_present; opc_JAL_present =
        p.opc_JAL_present; opc_SYSTEM_present = p.opc_SYSTEM_present;
        opc_OP_32_present = p.opc_OP_32_present; opc_OP_IMM_32_present =
        p.opc_OP_IMM_32_present; opc_AMO_present = p.opc_AMO_present;
        opc_OP_FP_present = p.opc_OP_FP_present; opc_MADD_present =
        p.opc_MADD_present; opc_MSUB_present = p.opc_MSUB_present;
        opc_NMSUB_present = p.opc_NMSUB_present; opc_NMADD_present =
        p.opc_NMADD_present; opc_LOAD_FP_present = p.opc_LOAD_FP_present;
        opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_AUIPC ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present =
        p.opc_JALR_present; opc_LOAD_present = p.opc_LOAD_present;
        opc_OP_IMM_present = p.opc_OP_IMM_present; opc_MISC_MEM_present =
        p.opc_MISC_MEM_present; opc_STORE_present = p.opc_STORE_present;
        opc_BRANCH_present = p.opc_BRANCH_present; opc_LUI_present =
        p.opc_LUI_present; opc_AUIPC_present = true; opc_JAL_present =
        p.opc_JAL_present; opc_SYSTEM_present = p.opc_SYSTEM_present;
        opc_OP_32_present = p.opc_OP_32_present; opc_OP_IMM_32_present =
        p.opc_OP_IMM_32_present; opc_AMO_present = p.opc_AMO_present;
        opc_OP_FP_present = p.opc_OP_FP_present; opc_MADD_present =
        p.opc_MADD_present; opc_MSUB_present = p.opc_MSUB_present;
        opc_NMSUB_present = p.opc_NMSUB_present; opc_NMADD_present =
        p.opc_NMADD_present; opc_LOAD_FP_present = p.opc_LOAD_FP_present;
        opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_JAL ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present =
        p.opc_JALR_present; opc_LOAD_present = p.opc_LOAD_present;
        opc_OP_IMM_present = p.opc_OP_IMM_present; opc_MISC_MEM_present =
        p.opc_MISC_MEM_present; opc_STORE_present = p.opc_STORE_present;
        opc_BRANCH_present = p.opc_BRANCH_present; opc_LUI_present =
        p.opc_LUI_present; opc_AUIPC_present = p.opc_AUIPC_present;
        opc_JAL_present = true; opc_SYSTEM_present = p.opc_SYSTEM_present;
        opc_OP_32_present = p.opc_OP_32_present; opc_OP_IMM_32_present =
        p.opc_OP_IMM_32_present; opc_AMO_present = p.opc_AMO_present;
        opc_OP_FP_present = p.opc_OP_FP_present; opc_MADD_present =
        p.opc_MADD_present; opc_MSUB_present = p.opc_MSUB_present;
        opc_NMSUB_present = p.opc_NMSUB_present; opc_NMADD_present =
        p.opc_NMADD_present; opc_LOAD_FP_present = p.opc_LOAD_FP_present;
        opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_SYSTEM ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present =
        p.opc_JALR_present; opc_LOAD_present = p.opc_LOAD_present;
        opc_OP_IMM_present = p.opc_OP_IMM_present; opc_MISC_MEM_present =
        p.opc_MISC_MEM_present; opc_STORE_present = p.opc_STORE_present;
        opc_BRANCH_present = p.opc_BRANCH_present; opc_LUI_present =
        p.opc_LUI_present; opc_AUIPC_present = p.opc_AUIPC_present;
        opc_JAL_present = p.opc_JAL_present; opc_SYSTEM_present = true;
        opc_OP_32_present = p.opc_OP_32_present; opc_OP_IMM_32_present =
        p.opc_OP_IMM_32_present; opc_AMO_present = p.opc_AMO_present;
        opc_OP_FP_present = p.opc_OP_FP_present; opc_MADD_present =
        p.opc_MADD_present; opc_MSUB_present = p.opc_MSUB_present;
        opc_NMSUB_present = p.opc_NMSUB_present; opc_NMADD_present =
        p.opc_NMADD_present; opc_LOAD_FP_present = p.opc_LOAD_FP_present;
        opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_OP_32 ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present =
        p.opc_JALR_present; opc_LOAD_present = p.opc_LOAD_present;
        opc_OP_IMM_present = p.opc_OP_IMM_present; opc_MISC_MEM_present =
        p.opc_MISC_MEM_present; opc_STORE_present = p.opc_STORE_present;
        opc_BRANCH_present = p.opc_BRANCH_present; opc_LUI_present =
        p.opc_LUI_present; opc_AUIPC_present = p.opc_AUIPC_present;
        opc_JAL_present = p.opc_JAL_present; opc_SYSTEM_present =
        p.opc_SYSTEM_present; opc_OP_32_present = true;
        opc_OP_IMM_32_present = p.opc_OP_IMM_32_present; opc_AMO_present =
        p.opc_AMO_present; opc_OP_FP_present = p.opc_OP_FP_present;
        opc_MADD_present = p.opc_MADD_present; opc_MSUB_present =
        p.opc_MSUB_present; opc_NMSUB_present = p.opc_NMSUB_present;
        opc_NMADD_present = p.opc_NMADD_present; opc_LOAD_FP_present =
        p.opc_LOAD_FP_present; opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_OP_IMM_32 ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present =
        p.opc_JALR_present; opc_LOAD_present = p.opc_LOAD_present;
        opc_OP_IMM_present = p.opc_OP_IMM_present; opc_MISC_MEM_present =
        p.opc_MISC_MEM_present; opc_STORE_present = p.opc_STORE_present;
        opc_BRANCH_present = p.opc_BRANCH_present; opc_LUI_present =
        p.opc_LUI_present; opc_AUIPC_present = p.opc_AUIPC_present;
        opc_JAL_present = p.opc_JAL_present; opc_SYSTEM_present =
        p.opc_SYSTEM_present; opc_OP_32_present = p.opc_OP_32_present;
        opc_OP_IMM_32_present = true; opc_AMO_present = p.opc_AMO_present;
        opc_OP_FP_present = p.opc_OP_FP_present; opc_MADD_present =
        p.opc_MADD_present; opc_MSUB_present = p.opc_MSUB_present;
        opc_NMSUB_present = p.opc_NMSUB_present; opc_NMADD_present =
        p.opc_NMADD_present; opc_LOAD_FP_present = p.opc_LOAD_FP_present;
        opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_AMO ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present =
        p.opc_JALR_present; opc_LOAD_present = p.opc_LOAD_present;
        opc_OP_IMM_present = p.opc_OP_IMM_present; opc_MISC_MEM_present =
        p.opc_MISC_MEM_present; opc_STORE_present = p.opc_STORE_present;
        opc_BRANCH_present = p.opc_BRANCH_present; opc_LUI_present =
        p.opc_LUI_present; opc_AUIPC_present = p.opc_AUIPC_present;
        opc_JAL_present = p.opc_JAL_present; opc_SYSTEM_present =
        p.opc_SYSTEM_present; opc_OP_32_present = p.opc_OP_32_present;
        opc_OP_IMM_32_present = p.opc_OP_IMM_32_present; opc_AMO_present =
        true; opc_OP_FP_present = p.opc_OP_FP_present; opc_MADD_present =
        p.opc_MADD_present; opc_MSUB_present = p.opc_MSUB_present;
        opc_NMSUB_present = p.opc_NMSUB_present; opc_NMADD_present =
        p.opc_NMADD_present; opc_LOAD_FP_present = p.opc_LOAD_FP_present;
        opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_OP_FP ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present =
        p.opc_JALR_present; opc_LOAD_present = p.opc_LOAD_present;
        opc_OP_IMM_present = p.opc_OP_IMM_present; opc_MISC_MEM_present =
        p.opc_MISC_MEM_present; opc_STORE_present = p.opc_STORE_present;
        opc_BRANCH_present = p.opc_BRANCH_present; opc_LUI_present =
        p.opc_LUI_present; opc_AUIPC_present = p.opc_AUIPC_present;
        opc_JAL_present = p.opc_JAL_present; opc_SYSTEM_present =
        p.opc_SYSTEM_present; opc_OP_32_present = p.opc_OP_32_present;
        opc_OP_IMM_32_present = p.opc_OP_IMM_32_present; opc_AMO_present =
        p.opc_AMO_present; opc_OP_FP_present = true; opc_MADD_present =
        p.opc_MADD_present; opc_MSUB_present = p.opc_MSUB_present;
        opc_NMSUB_present = p.opc_NMSUB_present; opc_NMADD_present =
        p.opc_NMADD_present; opc_LOAD_FP_present = p.opc_LOAD_FP_present;
        opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_MADD ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present =
        p.opc_JALR_present; opc_LOAD_present = p.opc_LOAD_present;
        opc_OP_IMM_present = p.opc_OP_IMM_present; opc_MISC_MEM_present =
        p.opc_MISC_MEM_present; opc_STORE_present = p.opc_STORE_present;
        opc_BRANCH_present = p.opc_BRANCH_present; opc_LUI_present =
        p.opc_LUI_present; opc_AUIPC_present = p.opc_AUIPC_present;
        opc_JAL_present = p.opc_JAL_present; opc_SYSTEM_present =
        p.opc_SYSTEM_present; opc_OP_32_present = p.opc_OP_32_present;
        opc_OP_IMM_32_present = p.opc_OP_IMM_32_present; opc_AMO_present =
        p.opc_AMO_present; opc_OP_FP_present = p.opc_OP_FP_present;
        opc_MADD_present = true; opc_MSUB_present = p.opc_MSUB_present;
        opc_NMSUB_present = p.opc_NMSUB_present; opc_NMADD_present =
        p.opc_NMADD_present; opc_LOAD_FP_present = p.opc_LOAD_FP_present;
        opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_MSUB ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present =
        p.opc_JALR_present; opc_LOAD_present = p.opc_LOAD_present;
        opc_OP_IMM_present = p.opc_OP_IMM_present; opc_MISC_MEM_present =
        p.opc_MISC_MEM_present; opc_STORE_present = p.opc_STORE_present;
        opc_BRANCH_present = p.opc_BRANCH_present; opc_LUI_present =
        p.opc_LUI_present; opc_AUIPC_present = p.opc_AUIPC_present;
        opc_JAL_present = p.opc_JAL_present; opc_SYSTEM_present =
        p.opc_SYSTEM_present; opc_OP_32_present = p.opc_OP_32_present;
        opc_OP_IMM_32_present = p.opc_OP_IMM_32_present; opc_AMO_present =
        p.opc_AMO_present; opc_OP_FP_present = p.opc_OP_FP_present;
        opc_MADD_present = p.opc_MADD_present; opc_MSUB_present = true;
        opc_NMSUB_present = p.opc_NMSUB_present; opc_NMADD_present =
        p.opc_NMADD_present; opc_LOAD_FP_present = p.opc_LOAD_FP_present;
        opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_NMSUB ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present =
        p.opc_JALR_present; opc_LOAD_present = p.opc_LOAD_present;
        opc_OP_IMM_present = p.opc_OP_IMM_present; opc_MISC_MEM_present =
        p.opc_MISC_MEM_present; opc_STORE_present = p.opc_STORE_present;
        opc_BRANCH_present = p.opc_BRANCH_present; opc_LUI_present =
        p.opc_LUI_present; opc_AUIPC_present = p.opc_AUIPC_present;
        opc_JAL_present = p.opc_JAL_present; opc_SYSTEM_present =
        p.opc_SYSTEM_present; opc_OP_32_present = p.opc_OP_32_present;
        opc_OP_IMM_32_present = p.opc_OP_IMM_32_present; opc_AMO_present =
        p.opc_AMO_present; opc_OP_FP_present = p.opc_OP_FP_present;
        opc_MADD_present = p.opc_MADD_present; opc_MSUB_present =
        p.opc_MSUB_present; opc_NMSUB_present = true; opc_NMADD_present =
        p.opc_NMADD_present; opc_LOAD_FP_present = p.opc_LOAD_FP_present;
        opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_NMADD ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present =
        p.opc_JALR_present; opc_LOAD_present = p.opc_LOAD_present;
        opc_OP_IMM_present = p.opc_OP_IMM_present; opc_MISC_MEM_present =
        p.opc_MISC_MEM_present; opc_STORE_present = p.opc_STORE_present;
        opc_BRANCH_present = p.opc_BRANCH_present; opc_LUI_present =
        p.opc_LUI_present; opc_AUIPC_present = p.opc_AUIPC_present;
        opc_JAL_present = p.opc_JAL_present; opc_SYSTEM_present =
        p.opc_SYSTEM_present; opc_OP_32_present = p.opc_OP_32_present;
        opc_OP_IMM_32_present = p.opc_OP_IMM_32_present; opc_AMO_present =
        p.opc_AMO_present; opc_OP_FP_present = p.opc_OP_FP_present;
        opc_MADD_present = p.opc_MADD_present; opc_MSUB_present =
        p.opc_MSUB_present; opc_NMSUB_present = p.opc_NMSUB_present;
        opc_NMADD_present = true; opc_LOAD_FP_present =
        p.opc_LOAD_FP_present; opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_LOAD_FP ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present =
        p.opc_JALR_present; opc_LOAD_present = p.opc_LOAD_present;
        opc_OP_IMM_present = p.opc_OP_IMM_present; opc_MISC_MEM_present =
        p.opc_MISC_MEM_present; opc_STORE_present = p.opc_STORE_present;
        opc_BRANCH_present = p.opc_BRANCH_present; opc_LUI_present =
        p.opc_LUI_present; opc_AUIPC_present = p.opc_AUIPC_present;
        opc_JAL_present = p.opc_JAL_present; opc_SYSTEM_present =
        p.opc_SYSTEM_present; opc_OP_32_present = p.opc_OP_32_present;
        opc_OP_IMM_32_present = p.opc_OP_IMM_32_present; opc_AMO_present =
        p.opc_AMO_present; opc_OP_FP_present = p.opc_OP_FP_present;
        opc_MADD_present = p.opc_MADD_present; opc_MSUB_present =
        p.opc_MSUB_present; opc_NMSUB_present = p.opc_NMSUB_present;
        opc_NMADD_present = p.opc_NMADD_present; opc_LOAD_FP_present = true;
        opc_STORE_FP_present = p.opc_STORE_FP_present }
    | Opc_STORE_FP ->
      { opc_OP_present = p.opc_OP_present; opc_JALR_present =
        p.opc_JALR_present; opc_LOAD_present = p.opc_LOAD_present;
        opc_OP_IMM_present = p.opc_OP_IMM_present; opc_MISC_MEM_present =
        p.opc_MISC_MEM_present; opc_STORE_present = p.opc_STORE_present;
        opc_BRANCH_present = p.opc_BRANCH_present; opc_LUI_present =
        p.opc_LUI_present; opc_AUIPC_present = p.opc_AUIPC_present;
        opc_JAL_present = p.opc_JAL_present; opc_SYSTEM_present =
        p.opc_SYSTEM_present; opc_OP_32_present = p.opc_OP_32_present;
        opc_OP_IMM_32_present = p.opc_OP_IMM_32_present; opc_AMO_present =
        p.opc_AMO_present; opc_OP_FP_present = p.opc_OP_FP_present;
        opc_MADD_present = p.opc_MADD_present; opc_MSUB_present =
        p.opc_MSUB_present; opc_NMSUB_present = p.opc_NMSUB_present;
        opc_NMADD_present = p.opc_NMADD_present; opc_LOAD_FP_present =
        p.opc_LOAD_FP_present; opc_STORE_FP_present = true }) instrs
    all_absent

(** val check_opcode_presence :
    present_opcodes -> opcode_name -> opcode_name option **)

let check_opcode_presence opcodes o = match o with
| Opc_OP -> if opcodes.opc_OP_present then Some o else None
| Opc_JALR -> if opcodes.opc_JALR_present then Some o else None
| Opc_LOAD -> if opcodes.opc_LOAD_present then Some o else None
| Opc_OP_IMM -> if opcodes.opc_OP_IMM_present then Some o else None
| Opc_MISC_MEM -> if opcodes.opc_MISC_MEM_present then Some o else None
| Opc_STORE -> if opcodes.opc_STORE_present then Some o else None
| Opc_BRANCH -> if opcodes.opc_BRANCH_present then Some o else None
| Opc_LUI -> if opcodes.opc_LUI_present then Some o else None
| Opc_AUIPC -> if opcodes.opc_AUIPC_present then Some o else None
| Opc_JAL -> if opcodes.opc_JAL_present then Some o else None
| Opc_SYSTEM -> if opcodes.opc_SYSTEM_present then Some o else None
| Opc_OP_32 -> if opcodes.opc_OP_32_present then Some o else None
| Opc_OP_IMM_32 -> if opcodes.opc_OP_IMM_32_present then Some o else None
| Opc_AMO -> if opcodes.opc_AMO_present then Some o else None
| Opc_OP_FP -> if opcodes.opc_OP_FP_present then Some o else None
| Opc_MADD -> if opcodes.opc_MADD_present then Some o else None
| Opc_MSUB -> if opcodes.opc_MSUB_present then Some o else None
| Opc_NMSUB -> if opcodes.opc_NMSUB_present then Some o else None
| Opc_NMADD -> if opcodes.opc_NMADD_present then Some o else None
| Opc_LOAD_FP -> if opcodes.opc_LOAD_FP_present then Some o else None
| Opc_STORE_FP -> if opcodes.opc_STORE_FP_present then Some o else None

(** val get_opcodes_from_present_opcodes :
    present_opcodes -> opcode_name list **)

let get_opcodes_from_present_opcodes opcodes =
  let all_opcodes =
    Opc_OP :: (Opc_JALR :: (Opc_LOAD :: (Opc_OP_IMM :: (Opc_MISC_MEM :: (Opc_STORE :: (Opc_BRANCH :: (Opc_LUI :: (Opc_AUIPC :: (Opc_JAL :: (Opc_SYSTEM :: (Opc_OP_32 :: (Opc_OP_IMM_32 :: (Opc_AMO :: (Opc_OP_FP :: (Opc_MADD :: (Opc_MSUB :: (Opc_NMSUB :: (Opc_NMADD :: (Opc_LOAD_FP :: (Opc_STORE_FP :: []))))))))))))))))))))
  in
  let after = map (check_opcode_presence opcodes) all_opcodes in
  fold_left (fun p t -> match t with
                        | Some x -> x :: p
                        | None -> p) after []

(** val get_opcodes_from_instructions_list :
    instruction list -> opcode_name list **)

let get_opcodes_from_instructions_list instrs =
  get_opcodes_from_present_opcodes
    (get_present_opcodes_from_instructions instrs)

(** val get_rs1_users : instruction list -> instruction list **)

let get_rs1_users instrs =
  filter (fun i -> has_rs1 (get_instruction_i_type i)) instrs

(** val get_rs2_users : instruction list -> instruction list **)

let get_rs2_users instrs =
  filter (fun i -> has_rs2 (get_instruction_i_type i)) instrs

(** val get_rd_users : instruction list -> instruction list **)

let get_rd_users instrs =
  filter (fun i -> has_rd (get_instruction_i_type i)) instrs

(** val optional_prepend :
    ('a1 -> bool) -> 'a1 -> 'a1 list sig0 -> 'a1 list sig0 **)

let optional_prepend f i l =
  let j = f i in if j then Exist (i :: (let Exist a = l in a)) else l

(** val custom_filter : ('a1 -> bool) -> 'a1 list -> 'a1 list sig0 **)

let custom_filter f input =
  let rec helper_f f0 i o =
    match i with
    | [] -> o
    | h :: t -> helper_f f0 t (optional_prepend f0 h o)
  in helper_f f input (Exist [])

(** val to_list_of_dependents :
    ('a1 -> bool) -> 'a1 list sig0 -> 'a1 sig0 list **)

let to_list_of_dependents f l =
  let rec helper_f f0 i o =
    match i with
    | [] -> o
    | h :: t -> helper_f f0 t ((Exist h) :: o)
  in helper_f f (let Exist a = l in a) []

(** val remove_dups : 'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 list **)

let remove_dups l eq =
  let rec helper_f i acc =
    match i with
    | [] -> acc
    | h :: t ->
      if existsb (eq h) t then helper_f t acc else helper_f t (h :: acc)
  in helper_f l []

(** val get_fcts3 : opcode_name -> instruction list -> fct3_type list **)

let get_fcts3 o instrs =
  let i = filter (fun i -> opcode_name_beq (instruction_opcode i) o) instrs in
  let i_fcts3 =
    custom_filter (fun i0 -> has_fct3 (get_instruction_i_type i0)) i
  in
  let i3 =
    to_list_of_dependents (fun i0 -> has_fct3 (get_instruction_i_type i0))
      i_fcts3
  in
  remove_dups (map (fun x -> instruction_fct3 (let Exist a = x in a)) i3)
    fct3_type_beq

(** val get_fcts2 :
    opcode_name -> fct3_type -> instruction list -> fct2_type list **)

let get_fcts2 o f3 instrs =
  let same_opcode =
    filter (fun i -> opcode_name_beq (instruction_opcode i) o) instrs
  in
  let same_opcode_and_fct3_present =
    to_list_of_dependents (fun i -> has_fct3 (get_instruction_i_type i))
      (custom_filter (fun i -> has_fct3 (get_instruction_i_type i))
        same_opcode)
  in
  let same_opcode_same_fct3_dependent =
    filter (fun i ->
      fct3_type_beq (instruction_fct3 (let Exist a = i in a)) f3)
      same_opcode_and_fct3_present
  in
  let same_opcode_same_fct3 =
    map (fun i -> let Exist a = i in a) same_opcode_same_fct3_dependent
  in
  let matching_and_fct2_present_dependent =
    custom_filter (fun i -> has_fct2 (get_instruction_i_type i))
      same_opcode_same_fct3
  in
  let matching_and_fct2_present =
    to_list_of_dependents (fun i -> has_fct2 (get_instruction_i_type i))
      matching_and_fct2_present_dependent
  in
  remove_dups
    (map (fun x -> instruction_fct2 (let Exist a = x in a))
      matching_and_fct2_present) fct2_type_beq

(** val get_fcts7 :
    opcode_name -> fct3_type -> instruction list -> fct7_type list **)

let get_fcts7 o f3 instrs =
  let same_opcode =
    filter (fun i -> opcode_name_beq (instruction_opcode i) o) instrs
  in
  let same_opcode_and_fct3_present =
    to_list_of_dependents (fun i -> has_fct3 (get_instruction_i_type i))
      (custom_filter (fun i -> has_fct3 (get_instruction_i_type i))
        same_opcode)
  in
  let same_opcode_same_fct3_dependent =
    filter (fun i ->
      fct3_type_beq (instruction_fct3 (let Exist a = i in a)) f3)
      same_opcode_and_fct3_present
  in
  let same_opcode_same_fct3 =
    map (fun i -> let Exist a = i in a) same_opcode_same_fct3_dependent
  in
  let matching_and_fct7_present_dependent =
    custom_filter (fun i -> has_fct7 (get_instruction_i_type i))
      same_opcode_same_fct3
  in
  let matching_and_fct7_present =
    to_list_of_dependents (fun i -> has_fct7 (get_instruction_i_type i))
      matching_and_fct7_present_dependent
  in
  remove_dups
    (map (fun x -> instruction_fct7 (let Exist a = x in a))
      matching_and_fct7_present) fct7_type_beq

(** val get_imm_fields_from_instructions :
    instruction list -> i_field list **)

let get_imm_fields_from_instructions instrs =
  let all_present_fields = get_i_fields_list_from_instructions instrs in
  filter (fun i ->
    match i with
    | ImmI -> true
    | ImmS -> true
    | ImmB -> true
    | ImmU -> true
    | ImmJ -> true
    | _ -> false) all_present_fields

(** val get_i_field_information_quantity : i_field -> int **)

let get_i_field_information_quantity f =
  let fp = get_i_field_properties f in
  if fp.is_sign_extended
  then Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         0)))))))))))))))))))))))))))))))
  else let sfs = fp.i_field_subfields in
       add fp.shift (fold_left (fun c sfp -> add c sfp.subfield_length) sfs 0)

(** val get_i_field_base_information_quantity : i_field -> int **)

let get_i_field_base_information_quantity f =
  let fp = get_i_field_properties f in
  let sfs = fp.i_field_subfields in
  add fp.shift (fold_left (fun c sfp -> add c sfp.subfield_length) sfs 0)

(** val get_i_fields_formatted_for_struct :
    instruction list -> (char list * type0) list **)

let get_i_fields_formatted_for_struct instrs =
  fold_left (fun l f -> ((get_i_field_name f), (Bits_t
    (get_i_field_information_quantity f))) :: l)
    (get_i_fields_list_from_instructions instrs) []

(** val get_inst_fields_struct_from_ISA : iSA -> type0 struct_sig' **)

let get_inst_fields_struct_from_ISA isa0 =
  { struct_name =
    ('i'::('n'::('s'::('t'::('F'::('i'::('e'::('l'::('d'::('s'::[]))))))))));
    struct_fields =
    (get_i_fields_formatted_for_struct (iSA_instructions_set isa0)) }

(** val isa : iSA **)

let isa =
  { iSA_base_standard = RV32I; iSA_extensions = [] }

(** val instructions : instruction list **)

let instructions =
  iSA_instructions_set isa

(** val imm_type : enum_sig **)

let imm_type =
  { enum_name = ('i'::('m'::('m'::('T'::('y'::('p'::('e'::[])))))));
    enum_size = (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))); enum_bitsize = (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))); enum_members =
    (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))) ('I'::('m'::('m'::('I'::[]))))
      (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
        ('I'::('m'::('m'::('S'::[]))))
        (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0))
          ('I'::('m'::('m'::('B'::[]))))
          (vect_cons (Pervasives.succ 0) ('I'::('m'::('m'::('U'::[]))))
            (Obj.magic vect_cons 0 ('I'::('m'::('m'::('J'::[])))) __)))));
    enum_bitpatterns =
    (vect_map (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0)))))
      (Bits.of_nat (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) 0
        (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
          (Pervasives.succ 0)
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0))
            (Pervasives.succ (Pervasives.succ 0))
            (vect_cons (Pervasives.succ 0) (Pervasives.succ (Pervasives.succ
              (Pervasives.succ 0)))
              (Obj.magic vect_cons 0 (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ 0)))) __)))))) }

(** val decoded_sig : type0 struct_sig' **)

let decoded_sig =
  { struct_name =
    ('d'::('e'::('c'::('o'::('d'::('e'::('d'::('I'::('n'::('s'::('t'::[])))))))))));
    struct_fields =
    ((('v'::('a'::('l'::('i'::('d'::('_'::('r'::('s'::('1'::[]))))))))),
    (Bits_t (Pervasives.succ
    0))) :: ((('v'::('a'::('l'::('i'::('d'::('_'::('r'::('s'::('2'::[]))))))))),
    (Bits_t (Pervasives.succ
    0))) :: ((('v'::('a'::('l'::('i'::('d'::('_'::('r'::('d'::[])))))))),
    (Bits_t (Pervasives.succ 0))) :: ((('l'::('e'::('g'::('a'::('l'::[]))))),
    (Bits_t (Pervasives.succ 0))) :: ((('i'::('n'::('s'::('t'::[])))),
    (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: ((('i'::('m'::('m'::('e'::('d'::('i'::('a'::('t'::('e'::('T'::('y'::('p'::('e'::[]))))))))))))),
    (Struct_t (maybe (Enum_t imm_type)))) :: [])))))) }

(** val inst_field : type0 struct_sig' **)

let inst_field =
  get_inst_fields_struct_from_ISA isa

(** val getFields :
    'a1 finiteType -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __)
    uaction) internalFunction **)

let getFields finite_reg0 =
  { int_name =
    ('g'::('e'::('t'::('F'::('i'::('e'::('l'::('d'::('s'::[])))))))));
    int_argspec =
    ((prod_of_argsig { arg_name = ('i'::('n'::('s'::('t'::[])))); arg_type =
       (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0))))))))))))))))))))))))))))))))) }) :: []);
    int_retSig = (Struct_t inst_field); int_body = (USugar (UStructInit
    (inst_field,
    (fold_left (fun a f ->
      let fp = get_i_field_properties f in
      let merge_actions = fun a1 a2 -> UBinop ((PrimUntyped.UBits2
        PrimUntyped.UConcat), a1, a2)
      in
      let manage_shift =
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> None)
          (fun n0 ->
          let x = Pervasives.succ n0 in
          Some (USugar (UConstBits (x, (Bits.of_N x 0)))))
          fp.shift
      in
      let slice_actions =
        let get_single_slice = fun sp -> UBinop ((PrimUntyped.UBits2
          (PrimUntyped.UIndexedSlice sp.subfield_length)), (UVar
          ('i'::('n'::('s'::('t'::[]))))), (USugar (UConstBits
          ((Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ 0))))),
          (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ 0))))) sp.first_bit)))))
        in
        let option_slices =
          fold_right (fun c a0 ->
            match a0 with
            | Some x -> Some (merge_actions (get_single_slice c) x)
            | None -> Some (get_single_slice c)) manage_shift
            (get_i_field_properties f).i_field_subfields
        in
        (match option_slices with
         | Some x -> x
         | None -> USugar USkip)
      in
      let manage_sign_extension = fun action1 ->
        if fp.is_sign_extended
        then let base_info_qtt = get_i_field_base_information_quantity f in
             USugar (UCallModule ((Obj.magic finite_reg0), id,
             (Obj.magic __),
             (Obj.magic signExtend base_info_qtt
               (sub (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ
                 0)))))))))))))))))))))))))))))))) base_info_qtt)),
             (action1 :: [])))
        else action1
      in
      let field_action = manage_sign_extension slice_actions in
      ((get_i_field_name f), (Obj.magic field_action)) :: a)
      (get_i_fields_list_from_instructions instructions) [])))) }

(** val isLegalInstruction :
    'a1 finiteType -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __)
    uaction) internalFunction **)

let isLegalInstruction finite_reg0 =
  { int_name =
    ('i'::('s'::('L'::('e'::('g'::('a'::('l'::('I'::('n'::('s'::('t'::('r'::('u'::('c'::('t'::('i'::('o'::('n'::[]))))))))))))))))));
    int_argspec = ((('i'::('n'::('s'::('t'::[])))), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: []); int_retSig = (Bits_t
    (Pervasives.succ 0)); int_body =
    (let opcodes = get_opcodes_from_instructions_list instructions in
     let generate_fct2_match = fun o f3 -> UBind
       (('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[])))))))))))))))))))))))),
       (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
       ('f'::('u'::('n'::('c'::('t'::('2'::[])))))))), (UVar
       ('f'::('i'::('e'::('l'::('d'::('s'::[]))))))))), (USugar (USwitch
       ((UVar
       ('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[]))))))))))))))))))))))))),
       (USugar (UConstBits ((Pervasives.succ 0),
       (Obj.magic vect_cons 0 false __)))),
       (map (fun f -> ((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
         0)), (Obj.magic fct2_bin f)))), (USugar (UConstBits
         ((Pervasives.succ 0), (Obj.magic vect_cons 0 true __))))))
         (get_fcts2 o f3 instructions))))))
     in
     let generate_fct7_match = fun o f3 -> UBind
       (('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[])))))))))))))))))))))))),
       (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
       ('f'::('u'::('n'::('c'::('t'::('7'::[])))))))), (UVar
       ('f'::('i'::('e'::('l'::('d'::('s'::[]))))))))), (USugar (USwitch
       ((UVar
       ('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[]))))))))))))))))))))))))),
       (USugar (UConstBits ((Pervasives.succ 0),
       (Obj.magic vect_cons 0 false __)))),
       (map (fun f -> ((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ 0))))))), (Obj.magic fct7_bin f)))), (USugar
         (UConstBits ((Pervasives.succ 0),
         (Obj.magic vect_cons 0 true __)))))) (get_fcts7 o f3 instructions))))))
     in
     let generate_fct3_match = fun o -> UBind
       (('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[])))))))))))))))))))))))),
       (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
       ('f'::('u'::('n'::('c'::('t'::('3'::[])))))))), (UVar
       ('f'::('i'::('e'::('l'::('d'::('s'::[]))))))))), (USugar (USwitch
       ((UVar
       ('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[]))))))))))))))))))))))))),
       (USugar (UConstBits ((Pervasives.succ 0),
       (Obj.magic vect_cons 0 false __)))),
       (map (fun f -> ((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
         (Pervasives.succ 0))), (Obj.magic fct3_bin f)))),
         (if has_fct2 (get_opcode_i_type o)
          then generate_fct2_match o f
          else if has_fct7 (get_opcode_i_type o)
               then generate_fct7_match o f
               else USugar (UConstBits ((Pervasives.succ 0),
                      (Obj.magic vect_cons 0 true __))))))
         (get_fcts3 o instructions))))))
     in
     UBind (('f'::('i'::('e'::('l'::('d'::('s'::[])))))), (USugar
     (UCallModule ((Obj.magic finite_reg0), (fun x -> Obj.magic x),
     (Obj.magic __), (Obj.magic getFields finite_reg0), ((UVar
     ('i'::('n'::('s'::('t'::[]))))) :: [])))), (UBind
     (('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[])))))))))))))))))))))))),
     (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
     ('o'::('p'::('c'::('o'::('d'::('e'::[])))))))), (UVar
     ('f'::('i'::('e'::('l'::('d'::('s'::[]))))))))), (USugar (USwitch ((UVar
     ('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[]))))))))))))))))))))))))),
     (USugar (UConstBits ((Pervasives.succ 0),
     (Obj.magic vect_cons 0 false __)))),
     (map (fun o -> ((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0))))))), (Obj.magic opcode_bin o)))),
       (if has_fct3 (get_opcode_i_type o)
        then generate_fct3_match o
        else USugar (UConstBits ((Pervasives.succ 0),
               (Obj.magic vect_cons 0 true __)))))) opcodes)))))))) }

(** val getImmediateType :
    'a1 finiteType -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __)
    uaction) internalFunction **)

let getImmediateType finite_reg0 =
  { int_name =
    ('g'::('e'::('t'::('I'::('m'::('m'::('e'::('d'::('i'::('a'::('t'::('e'::('T'::('y'::('p'::('e'::[]))))))))))))))));
    int_argspec = ((('i'::('n'::('s'::('t'::[])))), (Bits_t (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: []); int_retSig = (Struct_t
    (maybe (Enum_t imm_type))); int_body = (UBind
    (('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[])))))))))))))))))))))))),
    (UBinop ((PrimUntyped.UBits2 (PrimUntyped.UIndexedSlice (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))), (UVar
    ('i'::('n'::('s'::('t'::[]))))), (USugar (UConstBits ((Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) 0)))))), (USugar (USwitch
    ((UVar
    ('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[]))))))))))))))))))))))))),
    (USugar (UCallModule ((Obj.magic finite_reg0), (Obj.magic id),
    (Obj.magic __), (invalid (Enum_t imm_type)), []))),
    (let opcodes = get_opcodes_from_instructions_list instructions in
     map (fun o -> ((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0))))))), (Obj.magic opcode_bin o)))), (USugar
       (UStructInit ({ struct_name =
       ('m'::('a'::('y'::('b'::('e'::('_'::('i'::('m'::('m'::('T'::('y'::('p'::('e'::[])))))))))))));
       struct_fields = ((('v'::('a'::('l'::('i'::('d'::[]))))), (Bits_t
       (Pervasives.succ 0))) :: ((('d'::('a'::('t'::('a'::[])))), (Enum_t
       imm_type)) :: [])) }, ((('v'::('a'::('l'::('i'::('d'::[]))))), (USugar
       (UConstBits ((Pervasives.succ 0),
       (Obj.magic vect_cons 0 true __))))) :: ((('d'::('a'::('t'::('a'::[])))),
       (match o with
        | Opc_STORE ->
          USugar (UConstEnum (imm_type, ('I'::('m'::('m'::('S'::[]))))))
        | Opc_BRANCH ->
          USugar (UConstEnum (imm_type, ('I'::('m'::('m'::('B'::[]))))))
        | Opc_LUI ->
          USugar (UConstEnum (imm_type, ('I'::('m'::('m'::('U'::[]))))))
        | Opc_AUIPC ->
          USugar (UConstEnum (imm_type, ('I'::('m'::('m'::('U'::[]))))))
        | Opc_JAL ->
          USugar (UConstEnum (imm_type, ('I'::('m'::('m'::('J'::[]))))))
        | Opc_STORE_FP ->
          USugar (UConstEnum (imm_type, ('I'::('m'::('m'::('S'::[]))))))
        | _ -> USugar (UConstEnum (imm_type, ('I'::('m'::('m'::('I'::[])))))))) :: [])))))))
       opcodes)))))) }

(** val usesRS1 :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __) uaction)
    internalFunction **)

let usesRS1 =
  { int_name = ('u'::('s'::('e'::('s'::('R'::('S'::('1'::[])))))));
    int_argspec =
    ((prod_of_argsig { arg_name = ('i'::('n'::('s'::('t'::[])))); arg_type =
       (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0))))))))))))))))))))))))))))))))) }) :: []);
    int_retSig = (Bits_t (Pervasives.succ 0)); int_body = (UBind
    (('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[])))))))))))))))))))))))),
    (UBinop ((PrimUntyped.UBits2 (PrimUntyped.UIndexedSlice (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))), (UVar
    ('i'::('n'::('s'::('t'::[]))))), (USugar (UConstBits ((Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) 0)))))), (USugar (USwitch
    ((UVar
    ('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[]))))))))))))))))))))))))),
    (USugar (UConstBits ((Pervasives.succ 0),
    (Obj.magic vect_cons 0 false __)))),
    (let rs1_opcodes =
       get_opcodes_from_instructions_list (get_rs1_users instructions)
     in
     map (fun o -> ((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0))))))), (Obj.magic opcode_bin o)))), (USugar
       (UConstBits ((Pervasives.succ 0), (Obj.magic vect_cons 0 true __))))))
       rs1_opcodes)))))) }

(** val usesRS2 :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __) uaction)
    internalFunction **)

let usesRS2 =
  { int_name = ('u'::('s'::('e'::('s'::('R'::('S'::('2'::[])))))));
    int_argspec =
    ((prod_of_argsig { arg_name = ('i'::('n'::('s'::('t'::[])))); arg_type =
       (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0))))))))))))))))))))))))))))))))) }) :: []);
    int_retSig = (Bits_t (Pervasives.succ 0)); int_body = (UBind
    (('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[])))))))))))))))))))))))),
    (UBinop ((PrimUntyped.UBits2 (PrimUntyped.UIndexedSlice (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))), (UVar
    ('i'::('n'::('s'::('t'::[]))))), (USugar (UConstBits ((Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) 0)))))), (USugar (USwitch
    ((UVar
    ('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[]))))))))))))))))))))))))),
    (USugar (UConstBits ((Pervasives.succ 0),
    (Obj.magic vect_cons 0 false __)))),
    (let rs2_opcodes =
       get_opcodes_from_instructions_list (get_rs2_users instructions)
     in
     map (fun o -> ((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0))))))), (Obj.magic opcode_bin o)))), (USugar
       (UConstBits ((Pervasives.succ 0), (Obj.magic vect_cons 0 true __))))))
       rs2_opcodes)))))) }

(** val usesRD :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __) uaction)
    internalFunction **)

let usesRD =
  { int_name = ('u'::('s'::('e'::('s'::('R'::('D'::[])))))); int_argspec =
    ((prod_of_argsig { arg_name = ('i'::('n'::('s'::('t'::[])))); arg_type =
       (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0))))))))))))))))))))))))))))))))) }) :: []);
    int_retSig = (Bits_t (Pervasives.succ 0)); int_body = (UBind
    (('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[])))))))))))))))))))))))),
    (UBinop ((PrimUntyped.UBits2 (PrimUntyped.UIndexedSlice (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))), (UVar
    ('i'::('n'::('s'::('t'::[]))))), (USugar (UConstBits ((Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) 0)))))), (USugar (USwitch
    ((UVar
    ('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[]))))))))))))))))))))))))),
    (USugar (UConstBits ((Pervasives.succ 0),
    (Obj.magic vect_cons 0 false __)))),
    (let rd_opcodes =
       get_opcodes_from_instructions_list (get_rd_users instructions)
     in
     map (fun o -> ((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0))))))), (Obj.magic opcode_bin o)))), (USugar
       (UConstBits ((Pervasives.succ 0), (Obj.magic vect_cons 0 true __))))))
       rd_opcodes)))))) }

(** val decode_fun :
    'a1 finiteType -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __)
    uaction) internalFunction **)

let decode_fun finite_reg0 =
  { int_name =
    ('d'::('e'::('c'::('o'::('d'::('e'::('_'::('f'::('u'::('n'::[]))))))))));
    int_argspec =
    ((prod_of_argsig { arg_name =
       ('a'::('r'::('g'::('_'::('i'::('n'::('s'::('t'::[])))))))); arg_type =
       (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0))))))))))))))))))))))))))))))))) }) :: []);
    int_retSig = (Struct_t decoded_sig); int_body = (USugar (UStructInit
    (decoded_sig,
    (app
      (app
        (app
          (app
            (app
              ((('v'::('a'::('l'::('i'::('d'::('_'::('r'::('s'::('1'::[]))))))))),
              (USugar (UCallModule ((Obj.magic finite_reg0), (Obj.magic id),
              (Obj.magic __), (Obj.magic usesRS1), ((UVar
              ('a'::('r'::('g'::('_'::('i'::('n'::('s'::('t'::[]))))))))) :: []))))) :: [])
              ((('v'::('a'::('l'::('i'::('d'::('_'::('r'::('s'::('2'::[]))))))))),
              (USugar (UCallModule ((Obj.magic finite_reg0), (Obj.magic id),
              (Obj.magic __), (Obj.magic usesRS2), ((UVar
              ('a'::('r'::('g'::('_'::('i'::('n'::('s'::('t'::[]))))))))) :: []))))) :: []))
            ((('v'::('a'::('l'::('i'::('d'::('_'::('r'::('d'::[])))))))),
            (USugar (UCallModule ((Obj.magic finite_reg0), (Obj.magic id),
            (Obj.magic __), (Obj.magic usesRD), ((UVar
            ('a'::('r'::('g'::('_'::('i'::('n'::('s'::('t'::[]))))))))) :: []))))) :: []))
          ((('l'::('e'::('g'::('a'::('l'::[]))))), (USugar (UCallModule
          ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic __),
          (Obj.magic isLegalInstruction finite_reg0), ((UVar
          ('a'::('r'::('g'::('_'::('i'::('n'::('s'::('t'::[]))))))))) :: []))))) :: []))
        ((('i'::('n'::('s'::('t'::[])))), (UVar
        ('a'::('r'::('g'::('_'::('i'::('n'::('s'::('t'::[])))))))))) :: []))
      ((('i'::('m'::('m'::('e'::('d'::('i'::('a'::('t'::('e'::('T'::('y'::('p'::('e'::[]))))))))))))),
      (USugar (UCallModule ((Obj.magic finite_reg0), (Obj.magic id),
      (Obj.magic __), (Obj.magic getImmediateType finite_reg0), ((UVar
      ('a'::('r'::('g'::('_'::('i'::('n'::('s'::('t'::[]))))))))) :: []))))) :: []))))) }

(** val getImmediate :
    'a1 finiteType -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __)
    uaction) internalFunction **)

let getImmediate finite_reg0 =
  { int_name =
    ('g'::('e'::('t'::('I'::('m'::('m'::('e'::('d'::('i'::('a'::('t'::('e'::[]))))))))))));
    int_argspec =
    ((prod_of_argsig { arg_name = ('d'::('I'::('n'::('s'::('t'::[])))));
       arg_type = (Struct_t decoded_sig) }) :: []); int_retSig = (Bits_t
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))))))))))))))))))))))); int_body = (UBind
    (('i'::('m'::('m'::('_'::('t'::('y'::('p'::('e'::('_'::('v'::[])))))))))),
    (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
    ('i'::('m'::('m'::('e'::('d'::('i'::('a'::('t'::('e'::('T'::('y'::('p'::('e'::[]))))))))))))))),
    (UVar ('d'::('I'::('n'::('s'::('t'::[])))))))), (UIf ((UBinop
    ((PrimUntyped.UEq false), (UUnop ((PrimUntyped.UStruct1
    (PrimUntyped.UGetField ('v'::('a'::('l'::('i'::('d'::[]))))))), (UVar
    ('i'::('m'::('m'::('_'::('t'::('y'::('p'::('e'::('_'::('v'::[]))))))))))))),
    (USugar (UConstBits ((Pervasives.succ 0),
    (Obj.magic vect_cons 0 true __)))))), (UBind
    (('f'::('i'::('e'::('l'::('d'::('s'::[])))))), (USugar (UCallModule
    ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic __),
    (Obj.magic getFields finite_reg0), ((UUnop ((PrimUntyped.UStruct1
    (PrimUntyped.UGetField ('i'::('n'::('s'::('t'::[])))))), (UVar
    ('d'::('I'::('n'::('s'::('t'::[])))))))) :: [])))), (UBind
    (('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[])))))))))))))))))))))))),
    (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
    ('d'::('a'::('t'::('a'::[])))))), (UVar
    ('i'::('m'::('m'::('_'::('t'::('y'::('p'::('e'::('_'::('v'::[]))))))))))))),
    (USugar (USwitch ((UVar
    ('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[]))))))))))))))))))))))))),
    (USugar (UConstBits ((Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))))))))))))))))))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))))))))))))))))))))))))))))))) 0)))),
    (map (fun i ->
      match i with
      | ImmI ->
        ((USugar (UConstEnum (imm_type, ('I'::('m'::('m'::('I'::[]))))))),
          (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
          ('i'::('m'::('m'::('I'::[])))))), (UVar
          ('f'::('i'::('e'::('l'::('d'::('s'::[]))))))))))
      | ImmS ->
        ((USugar (UConstEnum (imm_type, ('I'::('m'::('m'::('S'::[]))))))),
          (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
          ('i'::('m'::('m'::('S'::[])))))), (UVar
          ('f'::('i'::('e'::('l'::('d'::('s'::[]))))))))))
      | ImmB ->
        ((USugar (UConstEnum (imm_type, ('I'::('m'::('m'::('B'::[]))))))),
          (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
          ('i'::('m'::('m'::('B'::[])))))), (UVar
          ('f'::('i'::('e'::('l'::('d'::('s'::[]))))))))))
      | ImmU ->
        ((USugar (UConstEnum (imm_type, ('I'::('m'::('m'::('U'::[]))))))),
          (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
          ('i'::('m'::('m'::('U'::[])))))), (UVar
          ('f'::('i'::('e'::('l'::('d'::('s'::[]))))))))))
      | ImmJ ->
        ((USugar (UConstEnum (imm_type, ('I'::('m'::('m'::('J'::[]))))))),
          (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
          ('i'::('m'::('m'::('J'::[])))))), (UVar
          ('f'::('i'::('e'::('l'::('d'::('s'::[]))))))))))
      | _ ->
        ((USugar (UConstBits ((Pervasives.succ 0),
          (Obj.magic vect_cons 0 false __)))), (USugar (UConstBits
          ((Pervasives.succ 0), (Obj.magic vect_cons 0 false __))))))
      (get_imm_fields_from_instructions instructions))))))))), (USugar
    (UConstBits ((Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))))))))))))))))))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))))))))))))))))))))))))))))))) 0)))))))) }

(** val alu32 :
    (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __) uaction)
    internalFunction **)

let alu32 =
  { int_name = ('a'::('l'::('u'::('3'::('2'::[]))))); int_argspec =
    (app
      ((prod_of_argsig { arg_name =
         ('f'::('u'::('n'::('c'::('t'::('3'::[])))))); arg_type = (Bits_t
         (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))) }) :: [])
      (app
        ((prod_of_argsig { arg_name =
           ('f'::('u'::('n'::('c'::('t'::('7'::[])))))); arg_type = (Bits_t
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ 0)))))))) }) :: [])
        (app
          ((prod_of_argsig { arg_name = ('a'::[]); arg_type = (Bits_t
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ
             0))))))))))))))))))))))))))))))))) }) :: [])
          ((prod_of_argsig { arg_name = ('b'::[]); arg_type = (Bits_t
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ
             0))))))))))))))))))))))))))))))))) }) :: [])))); int_retSig =
    (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))))))))))))))))))))); int_body = (UBind
    (('s'::('h'::('a'::('m'::('t'::[]))))), (UBinop ((PrimUntyped.UBits2
    (PrimUntyped.UIndexedSlice (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (UVar
    ('b'::[])), (USugar (UConstBits ((Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
    (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))) false
      (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
        false
        (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
          (vect_cons (Pervasives.succ 0) false
            (Obj.magic vect_cons 0 false __)))))))))), (UBind
    (('i'::('n'::('s'::('t'::('_'::('3'::('0'::[]))))))), (UBinop
    ((PrimUntyped.UBits2 PrimUntyped.USel), (UVar
    ('f'::('u'::('n'::('c'::('t'::('7'::[]))))))), (USugar (UConstBits
    ((Pervasives.succ (Pervasives.succ (Pervasives.succ 0))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
      ((fun p->1+2*p) ((fun p->2*p) 1)))))))), (UBind
    (('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[])))))))))))))))))))))))),
    (UVar ('f'::('u'::('n'::('c'::('t'::('3'::[]))))))), (USugar (USwitch
    ((UVar
    ('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[]))))))))))))))))))))))))),
    (USugar (UConstBits ((Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))))))))))))))))))),
    (Bits.of_nat (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))))))))))))))))))))))))))))))) 0)))),
    (app (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))), (Obj.magic funct3_ADD)))), (UIf ((UBinop
      ((PrimUntyped.UEq false), (UVar
      ('i'::('n'::('s'::('t'::('_'::('3'::('0'::[])))))))), (USugar
      (UConstBits ((Pervasives.succ 0), (Obj.magic vect_cons 0 true __)))))),
      (UBinop ((PrimUntyped.UBits2 PrimUntyped.UMinus), (UVar ('a'::[])),
      (UVar ('b'::[])))), (UBinop ((PrimUntyped.UBits2 PrimUntyped.UPlus),
      (UVar ('a'::[])), (UVar ('b'::[]))))))) :: [])
      (app (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0))), (Obj.magic funct3_SLL)))), (UBinop
        ((PrimUntyped.UBits2 PrimUntyped.ULsl), (UVar ('a'::[])), (UVar
        ('s'::('h'::('a'::('m'::('t'::[]))))))))) :: [])
        (app (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0))), (Obj.magic funct3_SLT)))), (UUnop
          ((PrimUntyped.UBits1 (PrimUntyped.UZExtL (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ
          0)))))))))))))))))))))))))))))))))), (UBinop ((PrimUntyped.UBits2
          (PrimUntyped.UCompare (true, CLt))), (UVar ('a'::[])), (UVar
          ('b'::[]))))))) :: [])
          (app (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
            (Pervasives.succ 0))), (Obj.magic funct3_SLTU)))), (UUnop
            ((PrimUntyped.UBits1 (PrimUntyped.UZExtL (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ 0)))))))))))))))))))))))))))))))))), (UBinop
            ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false, CLt))), (UVar
            ('a'::[])), (UVar ('b'::[]))))))) :: [])
            (app (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
              (Pervasives.succ 0))), (Obj.magic funct3_XOR)))), (UBinop
              ((PrimUntyped.UBits2 PrimUntyped.UXor), (UVar ('a'::[])), (UVar
              ('b'::[]))))) :: [])
              (app (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
                (Pervasives.succ 0))), (Obj.magic funct3_SRL)))), (UIf
                ((UBinop ((PrimUntyped.UEq false), (UVar
                ('i'::('n'::('s'::('t'::('_'::('3'::('0'::[])))))))), (USugar
                (UConstBits ((Pervasives.succ 0),
                (Obj.magic vect_cons 0 true __)))))), (UBinop
                ((PrimUntyped.UBits2 PrimUntyped.UAsr), (UVar ('a'::[])),
                (UVar ('s'::('h'::('a'::('m'::('t'::[])))))))), (UBinop
                ((PrimUntyped.UBits2 PrimUntyped.ULsr), (UVar ('a'::[])),
                (UVar ('s'::('h'::('a'::('m'::('t'::[]))))))))))) :: [])
                (app (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
                  (Pervasives.succ 0))), (Obj.magic funct3_OR)))), (UBinop
                  ((PrimUntyped.UBits2 PrimUntyped.UOr), (UVar ('a'::[])),
                  (UVar ('b'::[]))))) :: []) (((USugar (UConstBits
                  ((Pervasives.succ (Pervasives.succ (Pervasives.succ 0))),
                  (Obj.magic funct3_AND)))), (UBinop ((PrimUntyped.UBits2
                  PrimUntyped.UAnd), (UVar ('a'::[])), (UVar
                  ('b'::[]))))) :: []))))))))))))))))) }

(** val execALU32 :
    'a1 finiteType -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __)
    uaction) internalFunction **)

let execALU32 finite_reg0 =
  { int_name =
    ('e'::('x'::('e'::('c'::('A'::('L'::('U'::('3'::('2'::[])))))))));
    int_argspec =
    (app
      ((prod_of_argsig { arg_name = ('i'::('n'::('s'::('t'::[]))));
         arg_type = (Bits_t (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ
         0))))))))))))))))))))))))))))))))) }) :: [])
      (app
        ((prod_of_argsig { arg_name =
           ('r'::('s'::('1'::('_'::('v'::('a'::('l'::[]))))))); arg_type =
           (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ
           0))))))))))))))))))))))))))))))))) }) :: [])
        (app
          ((prod_of_argsig { arg_name =
             ('r'::('s'::('2'::('_'::('v'::('a'::('l'::[]))))))); arg_type =
             (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ
             0))))))))))))))))))))))))))))))))) }) :: [])
          (app
            ((prod_of_argsig { arg_name =
               ('i'::('m'::('m'::('_'::('v'::('a'::('l'::[])))))));
               arg_type = (Bits_t (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               0))))))))))))))))))))))))))))))))) }) :: [])
            ((prod_of_argsig { arg_name = ('p'::('c'::[])); arg_type =
               (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ
               0))))))))))))))))))))))))))))))))) }) :: []))))); int_retSig =
    (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))))))))))))))))))))); int_body = (UBind
    (('i'::('s'::('L'::('U'::('I'::[]))))), (UBinop ((PrimUntyped.UBits2
    PrimUntyped.UAnd), (UBinop ((PrimUntyped.UEq false), (UBinop
    ((PrimUntyped.UBits2 PrimUntyped.USel), (UVar
    ('i'::('n'::('s'::('t'::[]))))), (USugar (UConstBits ((Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) ((fun p->2*p) 1))))))),
    (USugar (UConstBits ((Pervasives.succ 0),
    (Obj.magic vect_cons 0 true __)))))), (UBinop ((PrimUntyped.UEq false),
    (UBinop ((PrimUntyped.UBits2 PrimUntyped.USel), (UVar
    ('i'::('n'::('s'::('t'::[]))))), (USugar (UConstBits ((Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) ((fun p->1+2*p) ((fun p->2*p)
      1)))))))), (USugar (UConstBits ((Pervasives.succ 0),
    (Obj.magic vect_cons 0 true __)))))))), (UBind
    (('i'::('s'::('A'::('U'::('I'::('P'::('C'::[]))))))), (UBinop
    ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UBinop ((PrimUntyped.UEq false),
    (UBinop ((PrimUntyped.UBits2 PrimUntyped.USel), (UVar
    ('i'::('n'::('s'::('t'::[]))))), (USugar (UConstBits ((Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) ((fun p->2*p) 1))))))),
    (USugar (UConstBits ((Pervasives.succ 0),
    (Obj.magic vect_cons 0 true __)))))), (UBinop ((PrimUntyped.UEq false),
    (UBinop ((PrimUntyped.UBits2 PrimUntyped.USel), (UVar
    ('i'::('n'::('s'::('t'::[]))))), (USugar (UConstBits ((Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) ((fun p->1+2*p) ((fun p->2*p)
      1)))))))), (USugar (UConstBits ((Pervasives.succ 0),
    (Obj.magic vect_cons 0 false __)))))))), (UBind
    (('i'::('s'::('I'::('M'::('M'::[]))))), (UBinop ((PrimUntyped.UEq false),
    (UBinop ((PrimUntyped.UBits2 PrimUntyped.USel), (UVar
    ('i'::('n'::('s'::('t'::[]))))), (USugar (UConstBits ((Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) ((fun p->1+2*p) ((fun p->2*p)
      1)))))))), (USugar (UConstBits ((Pervasives.succ 0),
    (Obj.magic vect_cons 0 false __)))))), (UBind
    (('r'::('d'::('_'::('v'::('a'::('l'::[])))))), (USugar (UConstBits
    ((Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))))))))))))))))))))))))))))))) 0)))), (USeq ((UIf
    ((UVar ('i'::('s'::('L'::('U'::('I'::[])))))), (UAssign
    (('r'::('d'::('_'::('v'::('a'::('l'::[])))))), (UVar
    ('i'::('m'::('m'::('_'::('v'::('a'::('l'::[])))))))))), (UIf ((UVar
    ('i'::('s'::('A'::('U'::('I'::('P'::('C'::[])))))))), (UAssign
    (('r'::('d'::('_'::('v'::('a'::('l'::[])))))), (UBinop
    ((PrimUntyped.UBits2 PrimUntyped.UPlus), (UVar ('p'::('c'::[]))), (UVar
    ('i'::('m'::('m'::('_'::('v'::('a'::('l'::[])))))))))))), (UBind
    (('a'::('l'::('u'::('_'::('s'::('r'::('c'::('1'::[])))))))), (UVar
    ('r'::('s'::('1'::('_'::('v'::('a'::('l'::[])))))))), (UBind
    (('a'::('l'::('u'::('_'::('s'::('r'::('c'::('2'::[])))))))), (UIf ((UVar
    ('i'::('s'::('I'::('M'::('M'::[])))))), (UVar
    ('i'::('m'::('m'::('_'::('v'::('a'::('l'::[])))))))), (UVar
    ('r'::('s'::('2'::('_'::('v'::('a'::('l'::[])))))))))), (UBind
    (('f'::('u'::('n'::('c'::('t'::('3'::[])))))), (UUnop
    ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
    ('f'::('u'::('n'::('c'::('t'::('3'::[])))))))), (USugar (UCallModule
    ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic __),
    (Obj.magic getFields finite_reg0), ((UVar
    ('i'::('n'::('s'::('t'::[]))))) :: [])))))), (UBind
    (('f'::('u'::('n'::('c'::('t'::('7'::[])))))), (UUnop
    ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
    ('f'::('u'::('n'::('c'::('t'::('7'::[])))))))), (USugar (UCallModule
    ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic __),
    (Obj.magic getFields finite_reg0), ((UVar
    ('i'::('n'::('s'::('t'::[]))))) :: [])))))), (UBind
    (('o'::('p'::('c'::('o'::('d'::('e'::[])))))), (UUnop
    ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
    ('o'::('p'::('c'::('o'::('d'::('e'::[])))))))), (USugar (UCallModule
    ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic __),
    (Obj.magic getFields finite_reg0), ((UVar
    ('i'::('n'::('s'::('t'::[]))))) :: [])))))), (USeq ((UIf ((UBinop
    ((PrimUntyped.UBits2 PrimUntyped.UOr), (UBinop ((PrimUntyped.UBits2
    PrimUntyped.UAnd), (UBinop ((PrimUntyped.UEq false), (UVar
    ('f'::('u'::('n'::('c'::('t'::('3'::[]))))))), (USugar (UConstBits
    ((Pervasives.succ (Pervasives.succ (Pervasives.succ 0))),
    (Obj.magic funct3_ADD)))))), (UVar
    ('i'::('s'::('I'::('M'::('M'::[])))))))), (UBinop ((PrimUntyped.UEq
    false), (UVar ('o'::('p'::('c'::('o'::('d'::('e'::[]))))))), (USugar
    (UConstBits ((Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))), (Obj.magic opcode_BRANCH)))))))), (UAssign
    (('f'::('u'::('n'::('c'::('t'::('7'::[])))))), (USugar (UConstBits
    ((Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))),
    (Obj.magic funct7_ADD)))))), (USugar (UConstBits (0, (Obj.magic __)))))),
    (UAssign (('r'::('d'::('_'::('v'::('a'::('l'::[])))))), (USugar
    (UCallModule ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic __),
    (Obj.magic alu32),
    (app ((UVar ('f'::('u'::('n'::('c'::('t'::('3'::[]))))))) :: [])
      (app ((UVar ('f'::('u'::('n'::('c'::('t'::('7'::[]))))))) :: [])
        (app ((UVar
          ('a'::('l'::('u'::('_'::('s'::('r'::('c'::('1'::[]))))))))) :: [])
          ((UVar
          ('a'::('l'::('u'::('_'::('s'::('r'::('c'::('2'::[]))))))))) :: []))))))))))))))))))))))))),
    (UVar ('r'::('d'::('_'::('v'::('a'::('l'::[]))))))))))))))))) }

(** val control_result : type0 struct_sig' **)

let control_result =
  { struct_name =
    ('c'::('o'::('n'::('t'::('r'::('o'::('l'::('_'::('r'::('e'::('s'::('u'::('l'::('t'::[]))))))))))))));
    struct_fields = ((('n'::('e'::('x'::('t'::('P'::('C'::[])))))), (Bits_t
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))) :: ((('t'::('a'::('k'::('e'::('n'::[]))))),
    (Bits_t (Pervasives.succ 0))) :: [])) }

(** val execControl32 :
    'a1 finiteType -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, 'a1, __)
    uaction) internalFunction **)

let execControl32 finite_reg0 =
  { int_name =
    ('e'::('x'::('e'::('c'::('C'::('o'::('n'::('t'::('r'::('o'::('l'::('3'::('2'::[])))))))))))));
    int_argspec =
    (app
      ((prod_of_argsig { arg_name = ('i'::('n'::('s'::('t'::[]))));
         arg_type = (Bits_t (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ
         0))))))))))))))))))))))))))))))))) }) :: [])
      (app
        ((prod_of_argsig { arg_name =
           ('r'::('s'::('1'::('_'::('v'::('a'::('l'::[]))))))); arg_type =
           (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ
           0))))))))))))))))))))))))))))))))) }) :: [])
        (app
          ((prod_of_argsig { arg_name =
             ('r'::('s'::('2'::('_'::('v'::('a'::('l'::[]))))))); arg_type =
             (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ
             0))))))))))))))))))))))))))))))))) }) :: [])
          (app
            ((prod_of_argsig { arg_name =
               ('i'::('m'::('m'::('_'::('v'::('a'::('l'::[])))))));
               arg_type = (Bits_t (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               0))))))))))))))))))))))))))))))))) }) :: [])
            ((prod_of_argsig { arg_name = ('p'::('c'::[])); arg_type =
               (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ
               0))))))))))))))))))))))))))))))))) }) :: []))))); int_retSig =
    (Struct_t control_result); int_body = (UBind
    (('i'::('s'::('C'::('o'::('n'::('t'::('r'::('o'::('l'::[]))))))))),
    (UBinop ((PrimUntyped.UEq false), (UBinop ((PrimUntyped.UBits2
    (PrimUntyped.UIndexedSlice (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))), (UVar ('i'::('n'::('s'::('t'::[]))))), (USugar
    (UConstBits ((Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) ((fun p->2*p) ((fun p->2*p)
      1)))))))), (USugar (UConstBits ((Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))),
    (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
      (vect_cons (Pervasives.succ 0) true (Obj.magic vect_cons 0 true __)))))))),
    (UBind (('i'::('s'::('J'::('A'::('L'::[]))))), (UBinop
    ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UBinop ((PrimUntyped.UEq false),
    (UBinop ((PrimUntyped.UBits2 PrimUntyped.USel), (UVar
    ('i'::('n'::('s'::('t'::[]))))), (USugar (UConstBits ((Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) ((fun p->2*p) 1))))))),
    (USugar (UConstBits ((Pervasives.succ 0),
    (Obj.magic vect_cons 0 true __)))))), (UBinop ((PrimUntyped.UEq false),
    (UBinop ((PrimUntyped.UBits2 PrimUntyped.USel), (UVar
    ('i'::('n'::('s'::('t'::[]))))), (USugar (UConstBits ((Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) ((fun p->1+2*p) 1))))))),
    (USugar (UConstBits ((Pervasives.succ 0),
    (Obj.magic vect_cons 0 true __)))))))), (UBind
    (('i'::('s'::('J'::('A'::('L'::('R'::[])))))), (UBinop
    ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UBinop ((PrimUntyped.UEq false),
    (UBinop ((PrimUntyped.UBits2 PrimUntyped.USel), (UVar
    ('i'::('n'::('s'::('t'::[]))))), (USugar (UConstBits ((Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) ((fun p->2*p) 1))))))),
    (USugar (UConstBits ((Pervasives.succ 0),
    (Obj.magic vect_cons 0 true __)))))), (UBinop ((PrimUntyped.UEq false),
    (UBinop ((PrimUntyped.UBits2 PrimUntyped.USel), (UVar
    ('i'::('n'::('s'::('t'::[]))))), (USugar (UConstBits ((Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) ((fun p->1+2*p) 1))))))),
    (USugar (UConstBits ((Pervasives.succ 0),
    (Obj.magic vect_cons 0 false __)))))))), (UBind
    (('i'::('n'::('c'::('P'::('C'::[]))))), (UBinop ((PrimUntyped.UBits2
    PrimUntyped.UPlus), (UVar ('p'::('c'::[]))), (USugar (UConstBits
    ((Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))))))))))))))))))))))))))))))) ((fun p->2*p)
      ((fun p->2*p) 1)))))))), (UBind
    (('f'::('u'::('n'::('c'::('t'::('3'::[])))))), (UUnop
    ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
    ('f'::('u'::('n'::('c'::('t'::('3'::[])))))))), (USugar (UCallModule
    ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic __),
    (Obj.magic getFields finite_reg0), ((UVar
    ('i'::('n'::('s'::('t'::[]))))) :: [])))))), (UBind
    (('t'::('a'::('k'::('e'::('n'::[]))))), (USugar (UConstBits
    ((Pervasives.succ 0), (Obj.magic vect_cons 0 true __)))), (UBind
    (('n'::('e'::('x'::('t'::('P'::('C'::[])))))), (UVar
    ('i'::('n'::('c'::('P'::('C'::[])))))), (USeq ((UIf ((UUnop
    ((PrimUntyped.UBits1 PrimUntyped.UNot), (UVar
    ('i'::('s'::('C'::('o'::('n'::('t'::('r'::('o'::('l'::[])))))))))))),
    (USeq ((UAssign (('t'::('a'::('k'::('e'::('n'::[]))))), (USugar
    (UConstBits ((Pervasives.succ 0), (Obj.magic vect_cons 0 false __)))))),
    (UAssign (('n'::('e'::('x'::('t'::('P'::('C'::[])))))), (UVar
    ('i'::('n'::('c'::('P'::('C'::[])))))))))), (UIf ((UVar
    ('i'::('s'::('J'::('A'::('L'::[])))))), (USeq ((UAssign
    (('t'::('a'::('k'::('e'::('n'::[]))))), (USugar (UConstBits
    ((Pervasives.succ 0), (Obj.magic vect_cons 0 true __)))))), (UAssign
    (('n'::('e'::('x'::('t'::('P'::('C'::[])))))), (UBinop
    ((PrimUntyped.UBits2 PrimUntyped.UPlus), (UVar ('p'::('c'::[]))), (UVar
    ('i'::('m'::('m'::('_'::('v'::('a'::('l'::[])))))))))))))), (UIf ((UVar
    ('i'::('s'::('J'::('A'::('L'::('R'::[]))))))), (USeq ((UAssign
    (('t'::('a'::('k'::('e'::('n'::[]))))), (USugar (UConstBits
    ((Pervasives.succ 0), (Obj.magic vect_cons 0 true __)))))), (UAssign
    (('n'::('e'::('x'::('t'::('P'::('C'::[])))))), (UBinop
    ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UBinop ((PrimUntyped.UBits2
    PrimUntyped.UPlus), (UVar
    ('r'::('s'::('1'::('_'::('v'::('a'::('l'::[])))))))), (UVar
    ('i'::('m'::('m'::('_'::('v'::('a'::('l'::[])))))))))), (UUnop
    ((PrimUntyped.UBits1 PrimUntyped.UNot), (USugar (UConstBits
    ((Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))),
    (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))))))))))))))))))))))))))))))) 1)))))))))))), (USeq
    ((UAssign (('t'::('a'::('k'::('e'::('n'::[]))))), (UBind
    (('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[])))))))))))))))))))))))),
    (UVar ('f'::('u'::('n'::('c'::('t'::('3'::[]))))))), (USugar (USwitch
    ((UVar
    ('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[]))))))))))))))))))))))))),
    (USugar (UConstBits ((Pervasives.succ 0),
    (Obj.magic vect_cons 0 false __)))),
    (app (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))), (Obj.magic funct3_BEQ)))), (UBinop
      ((PrimUntyped.UEq false), (UVar
      ('r'::('s'::('1'::('_'::('v'::('a'::('l'::[])))))))), (UVar
      ('r'::('s'::('2'::('_'::('v'::('a'::('l'::[]))))))))))) :: [])
      (app (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0))), (Obj.magic funct3_BNE)))), (UBinop
        ((PrimUntyped.UEq true), (UVar
        ('r'::('s'::('1'::('_'::('v'::('a'::('l'::[])))))))), (UVar
        ('r'::('s'::('2'::('_'::('v'::('a'::('l'::[]))))))))))) :: [])
        (app (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0))), (Obj.magic funct3_BLT)))), (UBinop
          ((PrimUntyped.UBits2 (PrimUntyped.UCompare (true, CLt))), (UVar
          ('r'::('s'::('1'::('_'::('v'::('a'::('l'::[])))))))), (UVar
          ('r'::('s'::('2'::('_'::('v'::('a'::('l'::[]))))))))))) :: [])
          (app (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
            (Pervasives.succ 0))), (Obj.magic funct3_BGE)))), (UUnop
            ((PrimUntyped.UBits1 PrimUntyped.UNot), (UBinop
            ((PrimUntyped.UBits2 (PrimUntyped.UCompare (true, CLt))), (UVar
            ('r'::('s'::('1'::('_'::('v'::('a'::('l'::[])))))))), (UVar
            ('r'::('s'::('2'::('_'::('v'::('a'::('l'::[]))))))))))))) :: [])
            (app (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
              (Pervasives.succ 0))), (Obj.magic funct3_BLTU)))), (UBinop
              ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false, CLt))),
              (UVar ('r'::('s'::('1'::('_'::('v'::('a'::('l'::[])))))))),
              (UVar
              ('r'::('s'::('2'::('_'::('v'::('a'::('l'::[]))))))))))) :: [])
              (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
              (Pervasives.succ 0))), (Obj.magic funct3_BGEU)))), (UUnop
              ((PrimUntyped.UBits1 PrimUntyped.UNot), (UBinop
              ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false, CLt))),
              (UVar ('r'::('s'::('1'::('_'::('v'::('a'::('l'::[])))))))),
              (UVar
              ('r'::('s'::('2'::('_'::('v'::('a'::('l'::[]))))))))))))) :: []))))))))))))),
    (UIf ((UVar ('t'::('a'::('k'::('e'::('n'::[])))))), (UAssign
    (('n'::('e'::('x'::('t'::('P'::('C'::[])))))), (UBinop
    ((PrimUntyped.UBits2 PrimUntyped.UPlus), (UVar ('p'::('c'::[]))), (UVar
    ('i'::('m'::('m'::('_'::('v'::('a'::('l'::[])))))))))))), (UAssign
    (('n'::('e'::('x'::('t'::('P'::('C'::[])))))), (UVar
    ('i'::('n'::('c'::('P'::('C'::[])))))))))))))))))), (USugar (UStructInit
    (control_result,
    (app ((('t'::('a'::('k'::('e'::('n'::[]))))), (UVar
      ('t'::('a'::('k'::('e'::('n'::[]))))))) :: [])
      ((('n'::('e'::('x'::('t'::('P'::('C'::[])))))), (UVar
      ('n'::('e'::('x'::('t'::('P'::('C'::[])))))))) :: []))))))))))))))))))))) }

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

(** val rv_external : rv_rules_t -> bool **)

let rv_external _ =
  false

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

(** val rv_schedule : (pos_t, rv_rules_t) scheduler **)

let rv_schedule =
  Cons (UpdateOnOff, (Cons (Writeback, (Cons (Execute, (Cons (Decode, (Cons
    (WaitImem, (Cons (Fetch, (Cons (Imem, (Cons (Dmem, (Cons (Tick, (Cons
    (EndExecution, Done)))))))))))))))))))

module Package =
 functor (C:Core) ->
 struct
  (** val circuits :
      (rv_rules_t, C._reg_t, C._ext_fn_t) register_update_circuitry **)

  let circuits =
    compile_scheduler C.coq_R C.coq_Sigma C.coq_FiniteType_reg_t show_string
      { show0 = (fun h ->
      match h with
      | Fetch -> 'F'::('e'::('t'::('c'::('h'::[]))))
      | Decode -> 'D'::('e'::('c'::('o'::('d'::('e'::[])))))
      | Execute -> 'E'::('x'::('e'::('c'::('u'::('t'::('e'::[]))))))
      | Writeback ->
        'W'::('r'::('i'::('t'::('e'::('b'::('a'::('c'::('k'::[]))))))))
      | WaitImem -> 'W'::('a'::('i'::('t'::('I'::('m'::('e'::('m'::[])))))))
      | Imem -> 'I'::('m'::('e'::('m'::[])))
      | Dmem -> 'D'::('m'::('e'::('m'::[])))
      | Tick -> 'T'::('i'::('c'::('k'::[])))
      | UpdateOnOff ->
        'U'::('p'::('d'::('a'::('t'::('e'::('O'::('n'::('O'::('f'::('f'::[]))))))))))
      | EndExecution ->
        'E'::('n'::('d'::('E'::('x'::('e'::('c'::('u'::('t'::('i'::('o'::('n'::[])))))))))))) }
      (opt_constprop (lower_R C.coq_R) (lower_Sigma C.coq_Sigma)) C.rv_rules
      rv_external rv_schedule

  (** val koika_package :
      (pos_t, var_t, fn_name_t, rv_rules_t, C._reg_t, C._ext_fn_t)
      koika_package_t **)

  let koika_package =
    { koika_var_names = show_string; koika_fn_names = show_string;
      koika_reg_names = C.coq_Show_reg_t; koika_reg_types = C.coq_R;
      koika_reg_init = C.r; koika_reg_finite = C.coq_FiniteType_reg_t;
      koika_ext_fn_types = C.coq_Sigma; koika_rules = C.rv_rules;
      koika_rule_external = rv_external; koika_rule_names = { show0 =
      (fun h ->
      match h with
      | Fetch -> 'F'::('e'::('t'::('c'::('h'::[]))))
      | Decode -> 'D'::('e'::('c'::('o'::('d'::('e'::[])))))
      | Execute -> 'E'::('x'::('e'::('c'::('u'::('t'::('e'::[]))))))
      | Writeback ->
        'W'::('r'::('i'::('t'::('e'::('b'::('a'::('c'::('k'::[]))))))))
      | WaitImem -> 'W'::('a'::('i'::('t'::('I'::('m'::('e'::('m'::[])))))))
      | Imem -> 'I'::('m'::('e'::('m'::[])))
      | Dmem -> 'D'::('m'::('e'::('m'::[])))
      | Tick -> 'T'::('i'::('c'::('k'::[])))
      | UpdateOnOff ->
        'U'::('p'::('d'::('a'::('t'::('e'::('O'::('n'::('O'::('f'::('f'::[]))))))))))
      | EndExecution ->
        'E'::('n'::('d'::('E'::('x'::('e'::('c'::('u'::('t'::('i'::('o'::('n'::[])))))))))))) };
      koika_scheduler = rv_schedule; koika_module_name =
      ('r'::('v'::('3'::('2'::[])))) }

  (** val package : interop_package_t **)

  let package =
    { ip_koika = (Obj.magic koika_package); ip_verilog = { vp_ext_fn_specs =
      (Obj.magic C.rv_ext_fn_rtl_specs) }; ip_sim = { sp_ext_fn_specs =
      (Obj.magic C.rv_ext_fn_sim_specs); sp_prelude = None } }
 end

module RVIParams =
 struct
  (** val coq_NREGS : int **)

  let coq_NREGS =
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))))))))))))))))))))))))))

  (** val coq_HAS_SHADOW_STACK : bool **)

  let coq_HAS_SHADOW_STACK =
    true
 end

module RV32I =
 struct
  module ShadowStack = ShadowStackF

  (** val mem_req : type0 struct_sig' **)

  let mem_req =
    { struct_name = ('m'::('e'::('m'::('_'::('r'::('e'::('q'::[])))))));
      struct_fields = ((('b'::('y'::('t'::('e'::('_'::('e'::('n'::[]))))))),
      (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))))) :: ((('a'::('d'::('d'::('r'::[])))), (Bits_t
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))))))))))))))))))))))))))))) :: ((('d'::('a'::('t'::('a'::[])))),
      (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))))))))))))))))))))))))))))))))) :: []))) }

  (** val mem_resp : type0 struct_sig' **)

  let mem_resp =
    { struct_name =
      ('m'::('e'::('m'::('_'::('r'::('e'::('s'::('p'::[]))))))));
      struct_fields = ((('b'::('y'::('t'::('e'::('_'::('e'::('n'::[]))))))),
      (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))))) :: ((('a'::('d'::('d'::('r'::[])))), (Bits_t
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))))))))))))))))))))))))))))) :: ((('d'::('a'::('t'::('a'::[])))),
      (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))))))))))))))))))))))))))))))))) :: []))) }

  (** val fetch_bookkeeping : type0 struct_sig' **)

  let fetch_bookkeeping =
    { struct_name =
      ('f'::('e'::('t'::('c'::('h'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[])))))))))))))))));
      struct_fields = ((('p'::('c'::[])), (Bits_t (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))))))))))))))))))))))))))))) :: ((('p'::('p'::('c'::[]))),
      (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ
      0)))))))))))))))))))))))))))))))))) :: ((('e'::('p'::('o'::('c'::('h'::[]))))),
      (Bits_t (Pervasives.succ 0))) :: []))) }

  (** val decode_bookkeeping : type0 struct_sig' **)

  let decode_bookkeeping =
    { struct_name =
      ('d'::('e'::('c'::('o'::('d'::('e'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[]))))))))))))))))));
      struct_fields = ((('p'::('c'::[])), (Bits_t (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))))))))))))))))))))))))))))) :: ((('p'::('p'::('c'::[]))),
      (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ
      0)))))))))))))))))))))))))))))))))) :: ((('e'::('p'::('o'::('c'::('h'::[]))))),
      (Bits_t (Pervasives.succ
      0))) :: ((('d'::('I'::('n'::('s'::('t'::[]))))), (Struct_t
      decoded_sig)) :: ((('r'::('v'::('a'::('l'::('1'::[]))))), (Bits_t
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))))))))))))))))))))))))))))) :: ((('r'::('v'::('a'::('l'::('2'::[]))))),
      (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))))))))))))))))))))))))))))))))) :: [])))))) }

  (** val execute_bookkeeping : type0 struct_sig' **)

  let execute_bookkeeping =
    { struct_name =
      ('e'::('x'::('e'::('c'::('u'::('t'::('e'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[])))))))))))))))))));
      struct_fields =
      ((('i'::('s'::('U'::('n'::('s'::('i'::('g'::('n'::('e'::('d'::[])))))))))),
      (Bits_t (Pervasives.succ 0))) :: ((('s'::('i'::('z'::('e'::[])))),
      (Bits_t (Pervasives.succ (Pervasives.succ
      0)))) :: ((('o'::('f'::('f'::('s'::('e'::('t'::[])))))), (Bits_t
      (Pervasives.succ (Pervasives.succ
      0)))) :: ((('n'::('e'::('w'::('r'::('d'::[]))))), (Bits_t
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))))))))))))))))))))))))))))) :: ((('d'::('I'::('n'::('s'::('t'::[]))))),
      (Struct_t decoded_sig)) :: []))))) }

  module FifoMemReq =
   struct
    (** val coq_T : type0 **)

    let coq_T =
      Struct_t mem_req
   end

  module MemReq = Fifo1Bypass(FifoMemReq)

  module FifoMemResp =
   struct
    (** val coq_T : type0 **)

    let coq_T =
      Struct_t mem_resp
   end

  module MemResp = Fifo1(FifoMemResp)

  module FifoUART =
   struct
    (** val coq_T : type0 **)

    let coq_T =
      Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0))))))))
   end

  module UARTReq = Fifo1Bypass(FifoUART)

  module UARTResp = Fifo1(FifoUART)

  module FifoFetch =
   struct
    (** val coq_T : type0 **)

    let coq_T =
      Struct_t fetch_bookkeeping
   end

  module Coq_fromFetch = Fifo1(FifoFetch)

  module Coq_waitFromFetch = Fifo1(FifoFetch)

  module FifoDecode =
   struct
    (** val coq_T : type0 **)

    let coq_T =
      Struct_t decode_bookkeeping
   end

  module Coq_fromDecode = Fifo1(FifoDecode)

  module FifoExecute =
   struct
    (** val coq_T : type0 **)

    let coq_T =
      Struct_t execute_bookkeeping
   end

  module Coq_fromExecute = Fifo1(FifoExecute)

  module RfParams =
   struct
    (** val idx_sz : int **)

    let idx_sz =
      Nat.log2_up RVIParams.coq_NREGS

    (** val coq_T : type0 **)

    let coq_T =
      Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0))))))))))))))))))))))))))))))))

    (** val init :
        (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
        (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
        (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
        (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
        vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
        vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
        vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
        vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
        vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
        vect_cons_t) vect_cons_t) vect_cons_t **)

    let init =
      Obj.magic vect_const (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))))))))))))))))))))))))))))))) false

    (** val read_style : var_t switch_style **)

    let read_style =
      read_style0 (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0))))))))))))))))))))))))))))))))

    (** val write_style : var_t switch_style **)

    let write_style =
      write_style0
   end

  module Rf = RfPow2(RfParams)

  module ScoreboardParams =
   struct
    (** val idx_sz : int **)

    let idx_sz =
      Nat.log2_up RVIParams.coq_NREGS

    (** val maxScore : int **)

    let maxScore =
      Pervasives.succ (Pervasives.succ (Pervasives.succ 0))
   end

  module Scoreboard = Scoreboard(ScoreboardParams)

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

  (** val reg_t_rect :
      (MemReq.reg_t -> 'a1) -> (MemResp.reg_t -> 'a1) -> (MemReq.reg_t ->
      'a1) -> (MemResp.reg_t -> 'a1) -> (Coq_fromFetch.reg_t -> 'a1) ->
      (Coq_waitFromFetch.reg_t -> 'a1) -> (Coq_fromDecode.reg_t -> 'a1) ->
      (Coq_fromExecute.reg_t -> 'a1) -> (Rf.reg_t -> 'a1) ->
      (ShadowStack.reg_t -> 'a1) -> (Scoreboard.reg_t -> 'a1) -> 'a1 -> 'a1
      -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> reg_t -> 'a1 **)

  let reg_t_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 = function
  | Coq_toIMem x -> f x
  | Coq_fromIMem x -> f0 x
  | Coq_toDMem x -> f1 x
  | Coq_fromDMem x -> f2 x
  | Coq_f2d x -> f3 x
  | Coq_f2dprim x -> f4 x
  | Coq_d2e x -> f5 x
  | Coq_e2w x -> f6 x
  | Coq_rf x -> f7 x
  | Coq_stack x -> f8 x
  | Coq_scoreboard x -> f9 x
  | Coq_cycle_count -> f10
  | Coq_instr_count -> f11
  | Coq_pc -> f12
  | Coq_epoch -> f13
  | Coq_debug -> f14
  | Coq_on_off -> f15
  | Coq_halt -> f16

  (** val reg_t_rec :
      (MemReq.reg_t -> 'a1) -> (MemResp.reg_t -> 'a1) -> (MemReq.reg_t ->
      'a1) -> (MemResp.reg_t -> 'a1) -> (Coq_fromFetch.reg_t -> 'a1) ->
      (Coq_waitFromFetch.reg_t -> 'a1) -> (Coq_fromDecode.reg_t -> 'a1) ->
      (Coq_fromExecute.reg_t -> 'a1) -> (Rf.reg_t -> 'a1) ->
      (ShadowStack.reg_t -> 'a1) -> (Scoreboard.reg_t -> 'a1) -> 'a1 -> 'a1
      -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> reg_t -> 'a1 **)

  let reg_t_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 = function
  | Coq_toIMem x -> f x
  | Coq_fromIMem x -> f0 x
  | Coq_toDMem x -> f1 x
  | Coq_fromDMem x -> f2 x
  | Coq_f2d x -> f3 x
  | Coq_f2dprim x -> f4 x
  | Coq_d2e x -> f5 x
  | Coq_e2w x -> f6 x
  | Coq_rf x -> f7 x
  | Coq_stack x -> f8 x
  | Coq_scoreboard x -> f9 x
  | Coq_cycle_count -> f10
  | Coq_instr_count -> f11
  | Coq_pc -> f12
  | Coq_epoch -> f13
  | Coq_debug -> f14
  | Coq_on_off -> f15
  | Coq_halt -> f16

  (** val coq_R : reg_t -> type0 **)

  let coq_R = function
  | Coq_toIMem r0 -> MemReq.coq_R r0
  | Coq_fromIMem r0 -> MemResp.coq_R r0
  | Coq_toDMem r0 -> MemReq.coq_R r0
  | Coq_fromDMem r0 -> MemResp.coq_R r0
  | Coq_f2d r0 -> Coq_fromFetch.coq_R r0
  | Coq_f2dprim r0 -> Coq_waitFromFetch.coq_R r0
  | Coq_d2e r0 -> Coq_fromDecode.coq_R r0
  | Coq_e2w r0 -> Coq_fromExecute.coq_R r0
  | Coq_rf r0 -> Rf.coq_R r0
  | Coq_stack r0 -> ShadowStack.coq_R r0
  | Coq_scoreboard r0 -> Scoreboard.coq_R r0
  | Coq_cycle_count ->
    Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))))))))))))))))))))))))))))))
  | Coq_instr_count ->
    Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))))))))))))))))))))))))))))))
  | Coq_pc ->
    Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))))))))))))))))))))))))))))))
  | _ -> Bits_t (Pervasives.succ 0)

  (** val r : reg_t -> type_denote **)

  let r = function
  | Coq_toIMem s -> MemReq.r s
  | Coq_fromIMem s -> MemResp.r s
  | Coq_toDMem s -> MemReq.r s
  | Coq_fromDMem s -> MemResp.r s
  | Coq_f2d s -> Coq_fromFetch.r s
  | Coq_f2dprim s -> Coq_waitFromFetch.r s
  | Coq_d2e s -> Coq_fromDecode.r s
  | Coq_e2w s -> Coq_fromExecute.r s
  | Coq_rf s -> Rf.r s
  | Coq_stack s -> ShadowStack.r s
  | Coq_scoreboard s -> Scoreboard.r s
  | Coq_cycle_count ->
    Bits.zero (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))))))))))))))))))))))))))))))
  | Coq_instr_count ->
    Bits.zero (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))))))))))))))))))))))))))))))
  | Coq_pc ->
    Bits.zero (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))))))))))))))))))))))))))))))
  | _ -> Bits.zero (Pervasives.succ 0)

  type memory =
  | Coq_imem
  | Coq_dmem

  (** val memory_rect : 'a1 -> 'a1 -> memory -> 'a1 **)

  let memory_rect f f0 = function
  | Coq_imem -> f
  | Coq_dmem -> f0

  (** val memory_rec : 'a1 -> 'a1 -> memory -> 'a1 **)

  let memory_rec f f0 = function
  | Coq_imem -> f
  | Coq_dmem -> f0

  type ext_fn_t =
  | Coq_ext_mem of memory
  | Coq_ext_uart_read
  | Coq_ext_uart_write
  | Coq_ext_led
  | Coq_ext_host_id
  | Coq_ext_finish

  (** val ext_fn_t_rect :
      (memory -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> ext_fn_t -> 'a1 **)

  let ext_fn_t_rect f f0 f1 f2 f3 f4 = function
  | Coq_ext_mem x -> f x
  | Coq_ext_uart_read -> f0
  | Coq_ext_uart_write -> f1
  | Coq_ext_led -> f2
  | Coq_ext_host_id -> f3
  | Coq_ext_finish -> f4

  (** val ext_fn_t_rec :
      (memory -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> ext_fn_t -> 'a1 **)

  let ext_fn_t_rec f f0 f1 f2 f3 f4 = function
  | Coq_ext_mem x -> f x
  | Coq_ext_uart_read -> f0
  | Coq_ext_uart_write -> f1
  | Coq_ext_led -> f2
  | Coq_ext_host_id -> f3
  | Coq_ext_finish -> f4

  (** val mem_input : type0 struct_sig' **)

  let mem_input =
    { struct_name =
      ('m'::('e'::('m'::('_'::('i'::('n'::('p'::('u'::('t'::[])))))))));
      struct_fields =
      ((('g'::('e'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[]))))))))),
      (Bits_t (Pervasives.succ
      0))) :: ((('p'::('u'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[]))))))))),
      (Bits_t (Pervasives.succ
      0))) :: ((('p'::('u'::('t'::('_'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))))))),
      (Struct_t mem_req)) :: []))) }

  (** val mem_output : type0 struct_sig' **)

  let mem_output =
    { struct_name =
      ('m'::('e'::('m'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))));
      struct_fields =
      ((('g'::('e'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[]))))))))),
      (Bits_t (Pervasives.succ
      0))) :: ((('p'::('u'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[]))))))))),
      (Bits_t (Pervasives.succ
      0))) :: ((('g'::('e'::('t'::('_'::('r'::('e'::('s'::('p'::('o'::('n'::('s'::('e'::[])))))))))))),
      (Struct_t mem_resp)) :: []))) }

  (** val uart_input : type0 **)

  let uart_input =
    Struct_t
      (maybe (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0))))))))))

  (** val uart_output : type0 **)

  let uart_output =
    Struct_t
      (maybe (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0))))))))))

  (** val led_input : type0 **)

  let led_input =
    Struct_t (maybe (Bits_t (Pervasives.succ 0)))

  (** val finish_input : type0 **)

  let finish_input =
    Struct_t
      (maybe (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0))))))))))

  (** val host_id : enum_sig **)

  let host_id =
    { enum_name = ('h'::('o'::('s'::('t'::('I'::('D'::[])))))); enum_size =
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))); enum_bitsize = (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0)))))))); enum_members =
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0))) ('F'::('P'::('G'::('A'::[]))))
        (vect_cons (Pervasives.succ (Pervasives.succ 0))
          ('N'::('o'::('H'::('o'::('s'::('t'::[]))))))
          (Obj.magic vect_cons (Pervasives.succ 0)
            ('V'::('e'::('r'::('i'::('l'::('a'::('t'::('o'::('r'::[])))))))))
            (vect_cons 0
              ('C'::('u'::('t'::('t'::('l'::('e'::('s'::('i'::('m'::[])))))))))
              (Obj.magic __))))); enum_bitpatterns =
      (vect_map (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0))))
        (Bits.of_nat (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0)))))))))
        (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0))) (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ
          0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          (vect_cons (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ 0))))))))
            (Obj.magic vect_cons (Pervasives.succ 0) (Pervasives.succ 0)
              (vect_cons 0 0 (Obj.magic __)))))) }

  (** val coq_Sigma : ext_fn_t -> type0 _Sig **)

  let coq_Sigma = function
  | Coq_ext_mem _ ->
    { argSigs = (Obj.magic vect_cons 0 (Struct_t mem_input) __); retSig =
      (Struct_t mem_output) }
  | Coq_ext_uart_read ->
    { argSigs = (Obj.magic vect_cons 0 (Bits_t (Pervasives.succ 0)) __);
      retSig = uart_output }
  | Coq_ext_uart_write ->
    { argSigs = (Obj.magic vect_cons 0 uart_input __); retSig = (Bits_t
      (Pervasives.succ 0)) }
  | Coq_ext_led ->
    { argSigs = (Obj.magic vect_cons 0 led_input __); retSig = (Bits_t
      (Pervasives.succ 0)) }
  | Coq_ext_host_id ->
    { argSigs = (Obj.magic vect_cons 0 (Bits_t (Pervasives.succ 0)) __);
      retSig = (Enum_t host_id) }
  | Coq_ext_finish ->
    { argSigs = (Obj.magic vect_cons 0 finish_input __); retSig = (Bits_t
      (Pervasives.succ 0)) }

  (** val update_on_off :
      (pos_t, var_t, fn_name_t, reg_t, ext_fn_t) uaction **)

  let update_on_off =
    UWrite (P1, Coq_on_off, (UBinop ((PrimUntyped.UBits2 PrimUntyped.UPlus),
      (URead (P0, Coq_on_off)), (USugar (UConstBits ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 true __)))))))

  (** val end_execution :
      (pos_t, var_t, fn_name_t, reg_t, ext_fn_t) uaction **)

  let end_execution =
    UBind (('r'::('e'::('s'::[]))), (UExternalCall (Coq_ext_finish, (USugar
      (UStructInit
      ((maybe (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ 0)))))))))),
      (app ((('v'::('a'::('l'::('i'::('d'::[]))))), (URead (P0,
        Coq_halt))) :: []) ((('d'::('a'::('t'::('a'::[])))), (USugar
        (UConstBits ((Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))))))),
        (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0)))))))) 1))))) :: []))))))), (UWrite (P0,
      Coq_debug, (UVar ('r'::('e'::('s'::[])))))))

  (** val fetch : (pos_t, var_t, fn_name_t, reg_t, ext_fn_t) uaction **)

  let fetch =
    USeq ((UIf ((UBinop ((PrimUntyped.UEq false), (URead (P0, Coq_halt)),
      (USugar (UConstBits ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 true __)))))), (UFail (Bits_t 0)), (USugar
      (UConstBits (0, (Obj.magic __)))))), (UBind (('p'::('c'::[])), (URead
      (P1, Coq_pc)), (UBind (('r'::('e'::('q'::[]))), (USugar (UStructInit
      (mem_req,
      (app
        (app ((('b'::('y'::('t'::('e'::('_'::('e'::('n'::[]))))))), (USugar
          (UConstBits ((Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0)))),
          (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ 0)))) 0))))) :: [])
          ((('a'::('d'::('d'::('r'::[])))), (UVar ('p'::('c'::[])))) :: []))
        ((('d'::('a'::('t'::('a'::[])))), (USugar (UConstBits
        ((Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0)))))))))))))))))))))))))))))))),
        (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0)))))))))))))))))))))))))))))))) 0))))) :: []))))),
      (UBind
      (('f'::('e'::('t'::('c'::('h'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[]))))))))))))))))),
      (USugar (UStructInit (fetch_bookkeeping,
      (app
        (app ((('p'::('c'::[])), (UVar ('p'::('c'::[])))) :: [])
          ((('p'::('p'::('c'::[]))), (UBinop ((PrimUntyped.UBits2
          PrimUntyped.UPlus), (UVar ('p'::('c'::[]))), (USugar (UConstBits
          ((Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0)))))))))))))))))))))))))))))))),
          (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ
            0)))))))))))))))))))))))))))))))) ((fun p->2*p) ((fun p->2*p) 1))))))))) :: []))
        ((('e'::('p'::('o'::('c'::('h'::[]))))), (URead (P1,
        Coq_epoch))) :: []))))), (USeq ((USeq ((USugar (UCallModule
      ((Obj.magic MemReq.coq_FiniteType_reg_t),
      (Obj.magic (fun x -> Coq_toIMem x)), (Obj.magic lift_empty),
      (Obj.magic MemReq.enq), ((UVar ('r'::('e'::('q'::[])))) :: [])))),
      (UWrite (P1, Coq_pc, (UBinop ((PrimUntyped.UBits2 PrimUntyped.UPlus),
      (UVar ('p'::('c'::[]))), (USugar (UConstBits ((Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))))))))))))))))))))))))))),
      (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))))))))))))))))))))))))))))))) ((fun p->2*p)
        ((fun p->2*p) 1)))))))))))), (USugar (UCallModule
      ((Obj.magic Coq_fromFetch.coq_FiniteType_reg_t),
      (Obj.magic (fun x -> Coq_f2d x)), (Obj.magic lift_empty),
      (Obj.magic Coq_fromFetch.enq), ((UVar
      ('f'::('e'::('t'::('c'::('h'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[])))))))))))))))))) :: [])))))))))))))

  (** val wait_imem : (pos_t, var_t, fn_name_t, reg_t, ext_fn_t) uaction **)

  let wait_imem =
    USeq ((UIf ((UBinop ((PrimUntyped.UEq false), (URead (P0, Coq_halt)),
      (USugar (UConstBits ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 true __)))))), (UFail (Bits_t 0)), (USugar
      (UConstBits (0, (Obj.magic __)))))), (UBind
      (('f'::('e'::('t'::('c'::('h'::('e'::('d'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[]))))))))))))))))))),
      (USugar (UCallModule ((Obj.magic Coq_fromFetch.coq_FiniteType_reg_t),
      (Obj.magic (fun x -> Coq_f2d x)), (Obj.magic lift_empty),
      (Obj.magic Coq_fromFetch.deq), []))), (USugar (UCallModule
      ((Obj.magic Coq_waitFromFetch.coq_FiniteType_reg_t),
      (Obj.magic (fun x -> Coq_f2dprim x)), (Obj.magic lift_empty),
      (Obj.magic Coq_waitFromFetch.enq), ((UVar
      ('f'::('e'::('t'::('c'::('h'::('e'::('d'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[])))))))))))))))))))) :: [])))))))

  (** val sliceReg :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let sliceReg =
    { int_name = ('s'::('l'::('i'::('c'::('e'::('R'::('e'::('g'::[]))))))));
      int_argspec =
      ((prod_of_argsig { arg_name = ('i'::('d'::('x'::[]))); arg_type =
         (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ 0)))))) }) :: []); int_retSig =
      (Bits_t (Nat.log2_up RVIParams.coq_NREGS)); int_body = (UBinop
      ((PrimUntyped.UBits2 (PrimUntyped.UIndexedSlice
      (Nat.log2_up RVIParams.coq_NREGS))), (UVar ('i'::('d'::('x'::[])))),
      (USugar (UConstBits ((Pervasives.succ (Pervasives.succ (Pervasives.succ
      0))),
      (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))) 0)))))) }

  (** val decode :
      reg_t finiteType -> ShadowStack.reg_t finiteType -> (pos_t, var_t,
      fn_name_t, reg_t, ext_fn_t) uaction **)

  let decode finite_reg0 _ =
    USeq ((UIf ((UBinop ((PrimUntyped.UEq false), (URead (P0, Coq_halt)),
      (USugar (UConstBits ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 true __)))))), (UFail (Bits_t 0)), (USugar
      (UConstBits (0, (Obj.magic __)))))), (UBind
      (('i'::('n'::('s'::('t'::('r'::[]))))), (USugar (UCallModule
      ((Obj.magic MemResp.coq_FiniteType_reg_t),
      (Obj.magic (fun x -> Coq_fromIMem x)), (Obj.magic lift_empty),
      (Obj.magic MemResp.deq), []))), (UBind
      (('i'::('n'::('s'::('t'::('r'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('d'::('a'::('t'::('a'::[])))))), (UVar
      ('i'::('n'::('s'::('t'::('r'::[])))))))), (UBind
      (('f'::('e'::('t'::('c'::('h'::('e'::('d'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[]))))))))))))))))))),
      (USugar (UCallModule
      ((Obj.magic Coq_waitFromFetch.coq_FiniteType_reg_t),
      (Obj.magic (fun x -> Coq_f2dprim x)), (Obj.magic lift_empty),
      (Obj.magic Coq_waitFromFetch.deq), []))), (UBind
      (('d'::('e'::('c'::('o'::('d'::('e'::('d'::('I'::('n'::('s'::('t'::[]))))))))))),
      (USugar (UCallModule ((Obj.magic finite_reg0), (Obj.magic id),
      (Obj.magic lift_empty), (Obj.magic decode_fun finite_reg0), ((UVar
      ('i'::('n'::('s'::('t'::('r'::[])))))) :: [])))), (UIf ((UBinop
      ((PrimUntyped.UEq false), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('e'::('p'::('o'::('c'::('h'::[]))))))), (UVar
      ('f'::('e'::('t'::('c'::('h'::('e'::('d'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[])))))))))))))))))))))),
      (URead (P1, Coq_epoch)))), (UBind
      (('r'::('s'::('1'::('_'::('i'::('d'::('x'::[]))))))), (UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('r'::('s'::('1'::[]))))), (USugar (UCallModule
      ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic lift_empty),
      (Obj.magic getFields finite_reg0), ((UVar
      ('i'::('n'::('s'::('t'::('r'::[])))))) :: [])))))), (UBind
      (('r'::('s'::('2'::('_'::('i'::('d'::('x'::[]))))))), (UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('r'::('s'::('2'::[]))))), (USugar (UCallModule
      ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic lift_empty),
      (Obj.magic getFields finite_reg0), ((UVar
      ('i'::('n'::('s'::('t'::('r'::[])))))) :: [])))))), (UBind
      (('s'::('c'::('o'::('r'::('e'::('1'::[])))))), (USugar (UCallModule
      ((Obj.magic Scoreboard.finite_reg),
      (Obj.magic (fun x -> Coq_scoreboard x)), (Obj.magic lift_empty),
      (Obj.magic Scoreboard.search), ((USugar (UCallModule
      ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic lift_empty),
      (Obj.magic sliceReg), ((UVar
      ('r'::('s'::('1'::('_'::('i'::('d'::('x'::[])))))))) :: [])))) :: [])))),
      (UBind (('s'::('c'::('o'::('r'::('e'::('2'::[])))))), (USugar
      (UCallModule ((Obj.magic Scoreboard.finite_reg),
      (Obj.magic (fun x -> Coq_scoreboard x)), (Obj.magic lift_empty),
      (Obj.magic Scoreboard.search), ((USugar (UCallModule
      ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic lift_empty),
      (Obj.magic sliceReg), ((UVar
      ('r'::('s'::('2'::('_'::('i'::('d'::('x'::[])))))))) :: [])))) :: [])))),
      (USeq ((USeq ((UIf ((UUnop ((PrimUntyped.UBits1 PrimUntyped.UNot),
      (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UBinop
      ((PrimUntyped.UEq false), (UVar
      ('s'::('c'::('o'::('r'::('e'::('1'::[]))))))), (USugar (UConstBits
      ((Pervasives.succ (Pervasives.succ 0)),
      (Obj.magic vect_cons (Pervasives.succ 0) false
        (vect_cons 0 false (Obj.magic __)))))))), (UBinop ((PrimUntyped.UEq
      false), (UVar ('s'::('c'::('o'::('r'::('e'::('2'::[]))))))), (USugar
      (UConstBits ((Pervasives.succ (Pervasives.succ 0)),
      (Obj.magic vect_cons (Pervasives.succ 0) false
        (vect_cons 0 false (Obj.magic __)))))))))))), (UFail (Bits_t 0)),
      (USugar (UConstBits (0, (Obj.magic __)))))), (UIf ((UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('v'::('a'::('l'::('i'::('d'::('_'::('r'::('d'::[])))))))))), (UVar
      ('d'::('e'::('c'::('o'::('d'::('e'::('d'::('I'::('n'::('s'::('t'::[])))))))))))))),
      (UBind (('r'::('d'::('_'::('i'::('d'::('x'::[])))))), (UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField ('r'::('d'::[])))),
      (USugar (UCallModule ((Obj.magic finite_reg0), (Obj.magic id),
      (Obj.magic lift_empty), (Obj.magic getFields finite_reg0), ((UVar
      ('i'::('n'::('s'::('t'::('r'::[])))))) :: [])))))), (USugar
      (UCallModule ((Obj.magic Scoreboard.finite_reg),
      (Obj.magic (fun x -> Coq_scoreboard x)), (Obj.magic lift_empty),
      (Obj.magic Scoreboard.insert), ((USugar (UCallModule
      ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic lift_empty),
      (Obj.magic sliceReg), ((UVar
      ('r'::('d'::('_'::('i'::('d'::('x'::[]))))))) :: [])))) :: [])))))),
      (USugar (UConstBits (0, (Obj.magic __)))))))), (UBind
      (('r'::('s'::('1'::[]))), (USugar (UCallModule
      ((Obj.magic Rf.finite_rf_reg), (Obj.magic (fun x -> Coq_rf x)),
      (Obj.magic lift_empty), (Obj.magic Rf.read_1), ((USugar (UCallModule
      ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic lift_empty),
      (Obj.magic sliceReg), ((UVar
      ('r'::('s'::('1'::('_'::('i'::('d'::('x'::[])))))))) :: [])))) :: [])))),
      (UBind (('r'::('s'::('2'::[]))), (USugar (UCallModule
      ((Obj.magic Rf.finite_rf_reg), (Obj.magic (fun x -> Coq_rf x)),
      (Obj.magic lift_empty), (Obj.magic Rf.read_1), ((USugar (UCallModule
      ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic lift_empty),
      (Obj.magic sliceReg), ((UVar
      ('r'::('s'::('2'::('_'::('i'::('d'::('x'::[])))))))) :: [])))) :: [])))),
      (UBind
      (('d'::('e'::('c'::('o'::('d'::('e'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[])))))))))))))))))),
      (USugar (UStructInit (decode_bookkeeping,
      (app
        (app
          (app
            (app
              (app ((('p'::('c'::[])), (UUnop ((PrimUntyped.UStruct1
                (PrimUntyped.UGetField ('p'::('c'::[])))), (UVar
                ('f'::('e'::('t'::('c'::('h'::('e'::('d'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[]))))))))))))))))))))))) :: [])
                ((('p'::('p'::('c'::[]))), (UUnop ((PrimUntyped.UStruct1
                (PrimUntyped.UGetField ('p'::('p'::('c'::[]))))), (UVar
                ('f'::('e'::('t'::('c'::('h'::('e'::('d'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[]))))))))))))))))))))))) :: []))
              ((('e'::('p'::('o'::('c'::('h'::[]))))), (UUnop
              ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
              ('e'::('p'::('o'::('c'::('h'::[]))))))), (UVar
              ('f'::('e'::('t'::('c'::('h'::('e'::('d'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[]))))))))))))))))))))))) :: []))
            ((('d'::('I'::('n'::('s'::('t'::[]))))), (UVar
            ('d'::('e'::('c'::('o'::('d'::('e'::('d'::('I'::('n'::('s'::('t'::[]))))))))))))) :: []))
          ((('r'::('v'::('a'::('l'::('1'::[]))))), (UVar
          ('r'::('s'::('1'::[]))))) :: []))
        ((('r'::('v'::('a'::('l'::('2'::[]))))), (UVar
        ('r'::('s'::('2'::[]))))) :: []))))), (USugar (UCallModule
      ((Obj.magic Coq_fromDecode.coq_FiniteType_reg_t),
      (Obj.magic (fun x -> Coq_d2e x)), (Obj.magic lift_empty),
      (Obj.magic Coq_fromDecode.enq), ((UVar
      ('d'::('e'::('c'::('o'::('d'::('e'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[]))))))))))))))))))) :: [])))))))))))))))))))),
      (USugar (UConstBits (0, (Obj.magic __)))))))))))))))

  (** val isMemoryInst :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let isMemoryInst =
    { int_name =
      ('i'::('s'::('M'::('e'::('m'::('o'::('r'::('y'::('I'::('n'::('s'::('t'::[]))))))))))));
      int_argspec =
      ((prod_of_argsig { arg_name = ('d'::('I'::('n'::('s'::('t'::[])))));
         arg_type = (Struct_t decoded_sig) }) :: []); int_retSig = (Bits_t
      (Pervasives.succ 0)); int_body = (UBinop ((PrimUntyped.UBits2
      PrimUntyped.UAnd), (UBinop ((PrimUntyped.UEq false), (UBinop
      ((PrimUntyped.UBits2 PrimUntyped.USel), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('i'::('n'::('s'::('t'::[])))))), (UVar
      ('d'::('I'::('n'::('s'::('t'::[])))))))), (USugar (UConstBits
      ((Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))),
      (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ 0))))) ((fun p->2*p)
        ((fun p->1+2*p) 1)))))))), (USugar (UConstBits ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 false __)))))), (UBinop ((PrimUntyped.UEq
      false), (UBinop ((PrimUntyped.UBits2 (PrimUntyped.UIndexedSlice
      (Pervasives.succ (Pervasives.succ 0)))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('i'::('n'::('s'::('t'::[])))))), (UVar
      ('d'::('I'::('n'::('s'::('t'::[])))))))), (USugar (UConstBits
      ((Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))),
      (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ 0))))) ((fun p->1+2*p) 1))))))),
      (USugar (UConstBits ((Pervasives.succ (Pervasives.succ 0)),
      (Obj.magic vect_cons (Pervasives.succ 0) false
        (vect_cons 0 false (Obj.magic __)))))))))) }

  (** val isControlInst :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let isControlInst =
    { int_name =
      ('i'::('s'::('C'::('o'::('n'::('t'::('r'::('o'::('l'::('I'::('n'::('s'::('t'::[])))))))))))));
      int_argspec =
      ((prod_of_argsig { arg_name = ('d'::('I'::('n'::('s'::('t'::[])))));
         arg_type = (Struct_t decoded_sig) }) :: []); int_retSig = (Bits_t
      (Pervasives.succ 0)); int_body = (UBinop ((PrimUntyped.UEq false),
      (UBinop ((PrimUntyped.UBits2 (PrimUntyped.UIndexedSlice
      (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('i'::('n'::('s'::('t'::[])))))), (UVar
      ('d'::('I'::('n'::('s'::('t'::[])))))))), (USugar (UConstBits
      ((Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))),
      (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ 0))))) ((fun p->2*p) ((fun p->2*p)
        1)))))))), (USugar (UConstBits ((Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))),
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
        (vect_cons (Pervasives.succ 0) true (Obj.magic vect_cons 0 true __)))))))) }

  (** val isJALXInst :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, __) uaction)
      internalFunction **)

  let isJALXInst =
    { int_name =
      ('i'::('s'::('J'::('A'::('L'::('X'::('I'::('n'::('s'::('t'::[]))))))))));
      int_argspec =
      ((prod_of_argsig { arg_name = ('d'::('I'::('n'::('s'::('t'::[])))));
         arg_type = (Struct_t decoded_sig) }) :: []); int_retSig = (Bits_t
      (Pervasives.succ 0)); int_body = (UBinop ((PrimUntyped.UBits2
      PrimUntyped.UAnd), (UBinop ((PrimUntyped.UEq false), (UBinop
      ((PrimUntyped.UBits2 (PrimUntyped.UIndexedSlice (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('i'::('n'::('s'::('t'::[])))))), (UVar
      ('d'::('I'::('n'::('s'::('t'::[])))))))), (USugar (UConstBits
      ((Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))),
      (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ 0))))) ((fun p->2*p) ((fun p->2*p)
        1)))))))), (USugar (UConstBits ((Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))),
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
        (vect_cons (Pervasives.succ 0) true (Obj.magic vect_cons 0 true __)))))))),
      (UBinop ((PrimUntyped.UEq false), (UBinop ((PrimUntyped.UBits2
      (PrimUntyped.UIndexedSlice (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('i'::('n'::('s'::('t'::[])))))), (UVar
      ('d'::('I'::('n'::('s'::('t'::[])))))))), (USugar (UConstBits
      ((Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))),
      (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ 0))))) 0)))))), (USugar (UConstBits
      ((Pervasives.succ (Pervasives.succ (Pervasives.succ 0))),
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
        (vect_cons (Pervasives.succ 0) true (Obj.magic vect_cons 0 true __)))))))))) }

  (** val execute_1 :
      reg_t finiteType -> ShadowStack.reg_t finiteType -> (pos_t, var_t,
      fn_name_t, reg_t, ext_fn_t) uaction **)

  let execute_1 finite_reg0 finite_reg_stack =
    UBind (('f'::('I'::('n'::('s'::('t'::[]))))), (UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('i'::('n'::('s'::('t'::[])))))), (UVar
      ('d'::('I'::('n'::('s'::('t'::[])))))))), (UBind
      (('f'::('u'::('n'::('c'::('t'::('3'::[])))))), (UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('f'::('u'::('n'::('c'::('t'::('3'::[])))))))), (USugar (UCallModule
      ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic lift_empty),
      (Obj.magic getFields finite_reg0), ((UVar
      ('f'::('I'::('n'::('s'::('t'::[])))))) :: [])))))), (UBind
      (('r'::('d'::('_'::('v'::('a'::('l'::[])))))), (UBinop
      ((PrimUntyped.UBits2 (PrimUntyped.UIndexedSlice (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0))))))), (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('i'::('n'::('s'::('t'::[])))))), (UVar
      ('d'::('I'::('n'::('s'::('t'::[])))))))), (USugar (UConstBits
      ((Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))),
      (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ 0))))) ((fun p->1+2*p)
        ((fun p->1+2*p) 1)))))))), (UBind
      (('r'::('s'::('1'::('_'::('v'::('a'::('l'::[]))))))), (UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('r'::('v'::('a'::('l'::('1'::[]))))))), (UVar
      ('d'::('e'::('c'::('o'::('d'::('e'::('d'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[])))))))))))))))))))))),
      (UBind (('r'::('s'::('2'::('_'::('v'::('a'::('l'::[]))))))), (UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('r'::('v'::('a'::('l'::('2'::[]))))))), (UVar
      ('d'::('e'::('c'::('o'::('d'::('e'::('d'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[])))))))))))))))))))))),
      (UBind (('i'::('m'::('m'::[]))), (USugar (UCallModule
      ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic lift_empty),
      (Obj.magic getImmediate finite_reg0), ((UVar
      ('d'::('I'::('n'::('s'::('t'::[])))))) :: [])))), (UBind
      (('p'::('c'::[])), (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('p'::('c'::[])))), (UVar
      ('d'::('e'::('c'::('o'::('d'::('e'::('d'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[])))))))))))))))))))))),
      (UBind (('d'::('a'::('t'::('a'::[])))), (USugar (UCallModule
      ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic lift_empty),
      (Obj.magic execALU32 finite_reg0),
      (app ((UVar ('f'::('I'::('n'::('s'::('t'::[])))))) :: [])
        (app ((UVar
          ('r'::('s'::('1'::('_'::('v'::('a'::('l'::[])))))))) :: [])
          (app ((UVar
            ('r'::('s'::('2'::('_'::('v'::('a'::('l'::[])))))))) :: [])
            (app ((UVar ('i'::('m'::('m'::[])))) :: []) ((UVar
              ('p'::('c'::[]))) :: [])))))))), (UBind
      (('i'::('s'::('U'::('n'::('s'::('i'::('g'::('n'::('e'::('d'::[])))))))))),
      (USugar (UConstBits ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 false __)))), (UBind
      (('s'::('i'::('z'::('e'::[])))), (UBinop ((PrimUntyped.UBits2
      (PrimUntyped.UIndexedSlice (Pervasives.succ (Pervasives.succ 0)))),
      (UVar ('f'::('u'::('n'::('c'::('t'::('3'::[]))))))), (USugar
      (UConstBits ((Pervasives.succ (Pervasives.succ 0)),
      (Bits.of_N (Pervasives.succ (Pervasives.succ 0)) 0)))))), (UBind
      (('a'::('d'::('d'::('r'::[])))), (UBinop ((PrimUntyped.UBits2
      PrimUntyped.UPlus), (UVar
      ('r'::('s'::('1'::('_'::('v'::('a'::('l'::[])))))))), (UVar
      ('i'::('m'::('m'::[])))))), (UBind
      (('o'::('f'::('f'::('s'::('e'::('t'::[])))))), (UBinop
      ((PrimUntyped.UBits2 (PrimUntyped.UIndexedSlice (Pervasives.succ
      (Pervasives.succ 0)))), (UVar ('a'::('d'::('d'::('r'::[]))))), (USugar
      (UConstBits ((Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))),
      (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ 0))))) 0)))))), (USeq ((UIf
      ((USugar (UCallModule ((Obj.magic finite_reg0), (Obj.magic id),
      (Obj.magic lift_empty), (Obj.magic isMemoryInst), ((UVar
      ('d'::('I'::('n'::('s'::('t'::[])))))) :: [])))), (UBind
      (('s'::('h'::('i'::('f'::('t'::('_'::('a'::('m'::('o'::('u'::('n'::('t'::[])))))))))))),
      (UBinop ((PrimUntyped.UBits2 PrimUntyped.UConcat), (UVar
      ('o'::('f'::('f'::('s'::('e'::('t'::[]))))))), (USugar (UConstBits
      ((Pervasives.succ (Pervasives.succ (Pervasives.succ 0))),
      (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))) 0)))))),
      (UBind (('i'::('s'::('_'::('w'::('r'::('i'::('t'::('e'::[])))))))),
      (UBinop ((PrimUntyped.UEq false), (UBinop ((PrimUntyped.UBits2
      PrimUntyped.USel), (UVar ('f'::('I'::('n'::('s'::('t'::[])))))),
      (USugar (UConstBits ((Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))),
      (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ 0))))) ((fun p->1+2*p)
        ((fun p->2*p) 1)))))))), (USugar (UConstBits ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 true __)))))), (UBind
      (('b'::('y'::('t'::('e'::('_'::('e'::('n'::[]))))))), (UIf ((UVar
      ('i'::('s'::('_'::('w'::('r'::('i'::('t'::('e'::[]))))))))), (UBinop
      ((PrimUntyped.UBits2 PrimUntyped.ULsl), (UBind
      (('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[])))))))))))))))))))))))),
      (UVar ('s'::('i'::('z'::('e'::[]))))), (USugar (USwitch ((UVar
      ('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[]))))))))))))))))))))))))),
      (UFail (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))))),
      (app (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ 0)),
        (Obj.magic vect_cons (Pervasives.succ 0) false
          (vect_cons 0 false (Obj.magic __)))))), (USugar (UConstBits
        ((Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0)))),
        (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0))) true
          (vect_cons (Pervasives.succ (Pervasives.succ 0)) false
            (Obj.magic vect_cons (Pervasives.succ 0) false
              (vect_cons 0 false (Obj.magic __))))))))) :: [])
        (app (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ 0)),
          (Obj.magic vect_cons (Pervasives.succ 0) true
            (vect_cons 0 false (Obj.magic __)))))), (USugar (UConstBits
          ((Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0)))),
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
            (Pervasives.succ 0))) true
            (vect_cons (Pervasives.succ (Pervasives.succ 0)) true
              (Obj.magic vect_cons (Pervasives.succ 0) false
                (vect_cons 0 false (Obj.magic __))))))))) :: []) (((USugar
          (UConstBits ((Pervasives.succ (Pervasives.succ 0)),
          (Obj.magic vect_cons (Pervasives.succ 0) false
            (vect_cons 0 true (Obj.magic __)))))), (USugar (UConstBits
          ((Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0)))),
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
            (Pervasives.succ 0))) true
            (vect_cons (Pervasives.succ (Pervasives.succ 0)) true
              (Obj.magic vect_cons (Pervasives.succ 0) true
                (vect_cons 0 true (Obj.magic __))))))))) :: [])))))))), (UVar
      ('o'::('f'::('f'::('s'::('e'::('t'::[]))))))))), (USugar (UConstBits
      ((Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))),
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0))) false
        (vect_cons (Pervasives.succ (Pervasives.succ 0)) false
          (Obj.magic vect_cons (Pervasives.succ 0) false
            (vect_cons 0 false (Obj.magic __)))))))))), (USeq ((USeq ((USeq
      ((UAssign (('d'::('a'::('t'::('a'::[])))), (UBinop ((PrimUntyped.UBits2
      PrimUntyped.ULsl), (UVar
      ('r'::('s'::('2'::('_'::('v'::('a'::('l'::[])))))))), (UVar
      ('s'::('h'::('i'::('f'::('t'::('_'::('a'::('m'::('o'::('u'::('n'::('t'::[]))))))))))))))))),
      (UAssign (('a'::('d'::('d'::('r'::[])))), (UBinop ((PrimUntyped.UBits2
      PrimUntyped.UConcat), (UBinop ((PrimUntyped.UBits2
      (PrimUntyped.UIndexedSlice (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))))))))))))))))))))))))))), (UVar
      ('a'::('d'::('d'::('r'::[]))))), (USugar (UConstBits ((Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0))))),
      (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ 0))))) ((fun p->2*p) 1))))))),
      (USugar (UConstBits ((Pervasives.succ (Pervasives.succ 0)),
      (Bits.of_N (Pervasives.succ (Pervasives.succ 0)) 0)))))))))), (UAssign
      (('i'::('s'::('U'::('n'::('s'::('i'::('g'::('n'::('e'::('d'::[])))))))))),
      (UBinop ((PrimUntyped.UBits2 PrimUntyped.USel), (UVar
      ('f'::('u'::('n'::('c'::('t'::('3'::[]))))))), (USugar (UConstBits
      ((Pervasives.succ (Pervasives.succ 0)),
      (Bits.of_N (Pervasives.succ (Pervasives.succ 0)) ((fun p->2*p) 1))))))))))),
      (USugar (UCallModule ((Obj.magic MemReq.coq_FiniteType_reg_t),
      (Obj.magic (fun x -> Coq_toDMem x)), (Obj.magic lift_empty),
      (Obj.magic MemReq.enq), ((USugar (UStructInit (mem_req,
      (app
        (app ((('b'::('y'::('t'::('e'::('_'::('e'::('n'::[]))))))), (UVar
          ('b'::('y'::('t'::('e'::('_'::('e'::('n'::[]))))))))) :: [])
          ((('a'::('d'::('d'::('r'::[])))), (UVar
          ('a'::('d'::('d'::('r'::[])))))) :: []))
        ((('d'::('a'::('t'::('a'::[])))), (UVar
        ('d'::('a'::('t'::('a'::[])))))) :: []))))) :: [])))))))))))), (UIf
      ((USugar (UCallModule ((Obj.magic finite_reg0), (Obj.magic id),
      (Obj.magic lift_empty), (Obj.magic isControlInst), ((UVar
      ('d'::('I'::('n'::('s'::('t'::[])))))) :: [])))), (USeq ((UAssign
      (('d'::('a'::('t'::('a'::[])))), (UBinop ((PrimUntyped.UBits2
      PrimUntyped.UPlus), (UVar ('p'::('c'::[]))), (USugar (UConstBits
      ((Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))))))))))))))))))))))))))),
      (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))))))))))))))))))))))))))))))) ((fun p->2*p)
        ((fun p->2*p) 1)))))))))),
      (if RVIParams.coq_HAS_SHADOW_STACK
       then UBind (('r'::('e'::('s'::[]))), (USugar (UConstBits
              ((Pervasives.succ 0), (Obj.magic vect_cons 0 false __)))),
              (UBind (('r'::('s'::('1'::[]))), (UBinop ((PrimUntyped.UBits2
              (PrimUntyped.UIndexedSlice (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))),
              (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
              ('i'::('n'::('s'::('t'::[])))))), (UVar
              ('d'::('I'::('n'::('s'::('t'::[])))))))), (USugar (UConstBits
              ((Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ 0))))),
              (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ 0))))) ((fun p->1+2*p)
                ((fun p->1+2*p) ((fun p->1+2*p) 1))))))))), (USeq ((UIf
              ((UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UBinop
              ((PrimUntyped.UEq false), (UBinop ((PrimUntyped.UBits2
              (PrimUntyped.UIndexedSlice (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ 0))))))))), (UUnop
              ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
              ('i'::('n'::('s'::('t'::[])))))), (UVar
              ('d'::('I'::('n'::('s'::('t'::[])))))))), (USugar (UConstBits
              ((Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ 0))))),
              (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ 0))))) 0)))))), (USugar
              (UConstBits ((Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ 0))))))),
              (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ 0)))))) true
                (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ 0))))) true
                  (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ 0)))) true
                    (vect_cons (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ 0))) true
                      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
                        0)) false
                        (vect_cons (Pervasives.succ 0) true
                          (Obj.magic vect_cons 0 true __)))))))))))), (UBinop
              ((PrimUntyped.UBits2 PrimUntyped.UOr), (UBinop
              ((PrimUntyped.UEq false), (UVar
              ('r'::('d'::('_'::('v'::('a'::('l'::[]))))))), (USugar
              (UConstBits ((Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ 0))))),
              (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ 0))))) 1)))))), (UBinop
              ((PrimUntyped.UEq false), (UVar
              ('r'::('d'::('_'::('v'::('a'::('l'::[]))))))), (USugar
              (UConstBits ((Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ 0))))),
              (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ 0))))) ((fun p->1+2*p)
                ((fun p->2*p) 1)))))))))))), (UAssign
              (('r'::('e'::('s'::[]))), (USugar (UCallModule
              ((Obj.magic finite_reg_stack),
              (Obj.magic (fun x -> Coq_stack x)), (Obj.magic lift_empty),
              (Obj.magic ShadowStack.push), ((UVar
              ('d'::('a'::('t'::('a'::[]))))) :: [])))))), (UIf ((UBinop
              ((PrimUntyped.UEq false), (UBinop ((PrimUntyped.UBits2
              (PrimUntyped.UIndexedSlice (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ 0))))))))), (UUnop
              ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
              ('i'::('n'::('s'::('t'::[])))))), (UVar
              ('d'::('I'::('n'::('s'::('t'::[])))))))), (USugar (UConstBits
              ((Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ 0))))),
              (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ 0))))) 0)))))), (USugar
              (UConstBits ((Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ 0))))))),
              (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ 0)))))) true
                (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ 0))))) true
                  (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ 0)))) true
                    (vect_cons (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ 0))) false
                      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
                        0)) false
                        (vect_cons (Pervasives.succ 0) true
                          (Obj.magic vect_cons 0 true __)))))))))))), (UIf
              ((UBinop ((PrimUntyped.UBits2 PrimUntyped.UOr), (UBinop
              ((PrimUntyped.UEq false), (UVar
              ('r'::('d'::('_'::('v'::('a'::('l'::[]))))))), (USugar
              (UConstBits ((Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ 0))))),
              (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ 0))))) 1)))))), (UBinop
              ((PrimUntyped.UEq false), (UVar
              ('r'::('d'::('_'::('v'::('a'::('l'::[]))))))), (USugar
              (UConstBits ((Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ 0))))),
              (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ 0))))) ((fun p->1+2*p)
                ((fun p->2*p) 1)))))))))), (UIf ((UBinop ((PrimUntyped.UBits2
              PrimUntyped.UOr), (UBinop ((PrimUntyped.UEq false), (UVar
              ('r'::('d'::('_'::('v'::('a'::('l'::[]))))))), (UVar
              ('r'::('s'::('1'::[])))))), (UBinop ((PrimUntyped.UBits2
              PrimUntyped.UAnd), (UBinop ((PrimUntyped.UEq true), (UVar
              ('r'::('s'::('1'::[])))), (USugar (UConstBits ((Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ 0))))),
              (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ 0))))) 1)))))), (UBinop
              ((PrimUntyped.UEq true), (UVar ('r'::('s'::('1'::[])))),
              (USugar (UConstBits ((Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
              (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ 0))))) ((fun p->1+2*p)
                ((fun p->2*p) 1)))))))))))), (UAssign
              (('r'::('e'::('s'::[]))), (USugar (UCallModule
              ((Obj.magic finite_reg_stack),
              (Obj.magic (fun x -> Coq_stack x)), (Obj.magic lift_empty),
              (Obj.magic ShadowStack.push), ((UVar
              ('d'::('a'::('t'::('a'::[]))))) :: [])))))), (USeq ((UAssign
              (('r'::('e'::('s'::[]))), (USugar (UCallModule
              ((Obj.magic finite_reg_stack),
              (Obj.magic (fun x -> Coq_stack x)), (Obj.magic lift_empty),
              (Obj.magic ShadowStack.pop), ((UVar
              ('a'::('d'::('d'::('r'::[]))))) :: [])))))), (UAssign
              (('r'::('e'::('s'::[]))), (UBinop ((PrimUntyped.UBits2
              PrimUntyped.UOr), (UVar ('r'::('e'::('s'::[])))), (USugar
              (UCallModule ((Obj.magic finite_reg_stack),
              (Obj.magic (fun x -> Coq_stack x)), (Obj.magic lift_empty),
              (Obj.magic ShadowStack.push), ((UVar
              ('d'::('a'::('t'::('a'::[]))))) :: [])))))))))))), (UIf
              ((UBinop ((PrimUntyped.UBits2 PrimUntyped.UOr), (UBinop
              ((PrimUntyped.UEq false), (UVar ('r'::('s'::('1'::[])))),
              (USugar (UConstBits ((Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
              (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ 0))))) 1)))))), (UBinop
              ((PrimUntyped.UEq false), (UVar ('r'::('s'::('1'::[])))),
              (USugar (UConstBits ((Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
              (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ 0))))) ((fun p->1+2*p)
                ((fun p->2*p) 1)))))))))), (UAssign (('r'::('e'::('s'::[]))),
              (USugar (UCallModule ((Obj.magic finite_reg_stack),
              (Obj.magic (fun x -> Coq_stack x)), (Obj.magic lift_empty),
              (Obj.magic ShadowStack.pop), ((UVar
              ('a'::('d'::('d'::('r'::[]))))) :: [])))))), (USugar
              (UConstBits (0, (Obj.magic __)))))))), (USugar (UConstBits (0,
              (Obj.magic __)))))))), (UWrite (P0, Coq_halt, (UVar
              ('r'::('e'::('s'::[])))))))))))
       else USugar (UConstBits (0, (Obj.magic __)))))), (USugar (UConstBits
      (0, (Obj.magic __)))))))), (UBind
      (('c'::('o'::('n'::('t'::('r'::('o'::('l'::('R'::('e'::('s'::('u'::('l'::('t'::[]))))))))))))),
      (USugar (UCallModule ((Obj.magic finite_reg0), (Obj.magic id),
      (Obj.magic lift_empty), (Obj.magic execControl32 finite_reg0),
      (app ((UVar ('f'::('I'::('n'::('s'::('t'::[])))))) :: [])
        (app ((UVar
          ('r'::('s'::('1'::('_'::('v'::('a'::('l'::[])))))))) :: [])
          (app ((UVar
            ('r'::('s'::('2'::('_'::('v'::('a'::('l'::[])))))))) :: [])
            (app ((UVar ('i'::('m'::('m'::[])))) :: []) ((UVar
              ('p'::('c'::[]))) :: [])))))))), (UBind
      (('n'::('e'::('x'::('t'::('P'::('c'::[])))))), (UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('n'::('e'::('x'::('t'::('P'::('C'::[])))))))), (UVar
      ('c'::('o'::('n'::('t'::('r'::('o'::('l'::('R'::('e'::('s'::('u'::('l'::('t'::[])))))))))))))))),
      (USeq ((UIf ((UBinop ((PrimUntyped.UEq true), (UVar
      ('n'::('e'::('x'::('t'::('P'::('c'::[]))))))), (UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('p'::('p'::('c'::[]))))), (UVar
      ('d'::('e'::('c'::('o'::('d'::('e'::('d'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[])))))))))))))))))))))))),
      (USeq ((UWrite (P0, Coq_epoch, (UBinop ((PrimUntyped.UBits2
      PrimUntyped.UPlus), (URead (P0, Coq_epoch)), (USugar (UConstBits
      ((Pervasives.succ 0), (Obj.magic vect_cons 0 true __)))))))), (UWrite
      (P0, Coq_pc, (UVar ('n'::('e'::('x'::('t'::('P'::('c'::[]))))))))))),
      (USugar (UConstBits (0, (Obj.magic __)))))), (UBind
      (('e'::('x'::('e'::('c'::('u'::('t'::('e'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[]))))))))))))))))))),
      (USugar (UStructInit (execute_bookkeeping,
      (app
        (app
          (app
            (app
              ((('i'::('s'::('U'::('n'::('s'::('i'::('g'::('n'::('e'::('d'::[])))))))))),
              (UVar
              ('i'::('s'::('U'::('n'::('s'::('i'::('g'::('n'::('e'::('d'::[])))))))))))) :: [])
              ((('s'::('i'::('z'::('e'::[])))), (UVar
              ('s'::('i'::('z'::('e'::[])))))) :: []))
            ((('o'::('f'::('f'::('s'::('e'::('t'::[])))))), (UVar
            ('o'::('f'::('f'::('s'::('e'::('t'::[])))))))) :: []))
          ((('n'::('e'::('w'::('r'::('d'::[]))))), (UVar
          ('d'::('a'::('t'::('a'::[])))))) :: []))
        ((('d'::('I'::('n'::('s'::('t'::[]))))), (UUnop
        ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
        ('d'::('I'::('n'::('s'::('t'::[]))))))), (UVar
        ('d'::('e'::('c'::('o'::('d'::('e'::('d'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[]))))))))))))))))))))))) :: []))))),
      (USugar (UCallModule ((Obj.magic Coq_fromExecute.coq_FiniteType_reg_t),
      (Obj.magic (fun x -> Coq_e2w x)), (Obj.magic lift_empty),
      (Obj.magic Coq_fromExecute.enq), ((UVar
      ('e'::('x'::('e'::('c'::('u'::('t'::('e'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[])))))))))))))))))))) :: [])))))))))))))))))))))))))))))))))))))

  (** val execute :
      reg_t finiteType -> ShadowStack.reg_t finiteType -> (pos_t, var_t,
      fn_name_t, reg_t, ext_fn_t) uaction **)

  let execute finite_reg0 finite_reg_stack =
    USeq ((UIf ((UBinop ((PrimUntyped.UEq false), (URead (P0, Coq_halt)),
      (USugar (UConstBits ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 true __)))))), (UFail (Bits_t 0)), (USugar
      (UConstBits (0, (Obj.magic __)))))), (UBind
      (('d'::('e'::('c'::('o'::('d'::('e'::('d'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[]))))))))))))))))))),
      (USugar (UCallModule ((Obj.magic Coq_fromDecode.coq_FiniteType_reg_t),
      (Obj.magic (fun x -> Coq_d2e x)), (Obj.magic lift_empty),
      (Obj.magic Coq_fromDecode.deq), []))), (UIf ((UBinop ((PrimUntyped.UEq
      false), (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('e'::('p'::('o'::('c'::('h'::[]))))))), (UVar
      ('d'::('e'::('c'::('o'::('d'::('e'::('d'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[])))))))))))))))))))))),
      (URead (P0, Coq_epoch)))), (UBind
      (('d'::('I'::('n'::('s'::('t'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('d'::('I'::('n'::('s'::('t'::[]))))))), (UVar
      ('d'::('e'::('c'::('o'::('d'::('e'::('d'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[])))))))))))))))))))))),
      (UIf ((UBinop ((PrimUntyped.UEq false), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('l'::('e'::('g'::('a'::('l'::[]))))))), (UVar
      ('d'::('I'::('n'::('s'::('t'::[])))))))), (USugar (UConstBits
      ((Pervasives.succ 0), (Obj.magic vect_cons 0 false __)))))), (USeq
      ((UWrite (P0, Coq_epoch, (UBinop ((PrimUntyped.UBits2
      PrimUntyped.UPlus), (URead (P0, Coq_epoch)), (USugar (UConstBits
      ((Pervasives.succ 0), (Obj.magic vect_cons 0 true __)))))))), (UWrite
      (P0, Coq_pc, (USugar (UConstBits ((Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))))))))))))))),
      (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))))))))))))))))))))))))))))))) 0)))))))),
      (execute_1 finite_reg0 finite_reg_stack))))), (USugar (UConstBits (0,
      (Obj.magic __)))))))))

  (** val writeback :
      reg_t finiteType -> ShadowStack.reg_t finiteType -> (pos_t, var_t,
      fn_name_t, reg_t, ext_fn_t) uaction **)

  let writeback finite_reg0 _ =
    USeq ((UIf ((UBinop ((PrimUntyped.UEq false), (URead (P0, Coq_halt)),
      (USugar (UConstBits ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 true __)))))), (UFail (Bits_t 0)), (USugar
      (UConstBits (0, (Obj.magic __)))))), (UBind
      (('e'::('x'::('e'::('c'::('u'::('t'::('e'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[]))))))))))))))))))),
      (USugar (UCallModule ((Obj.magic Coq_fromExecute.coq_FiniteType_reg_t),
      (Obj.magic (fun x -> Coq_e2w x)), (Obj.magic lift_empty),
      (Obj.magic Coq_fromExecute.deq), []))), (UBind
      (('d'::('I'::('n'::('s'::('t'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('d'::('I'::('n'::('s'::('t'::[]))))))), (UVar
      ('e'::('x'::('e'::('c'::('u'::('t'::('e'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[])))))))))))))))))))))),
      (UBind (('d'::('a'::('t'::('a'::[])))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('n'::('e'::('w'::('r'::('d'::[]))))))), (UVar
      ('e'::('x'::('e'::('c'::('u'::('t'::('e'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[])))))))))))))))))))))),
      (UBind (('f'::('i'::('e'::('l'::('d'::('s'::[])))))), (USugar
      (UCallModule ((Obj.magic finite_reg0), (Obj.magic id),
      (Obj.magic lift_empty), (Obj.magic getFields finite_reg0), ((UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('i'::('n'::('s'::('t'::[])))))), (UVar
      ('d'::('I'::('n'::('s'::('t'::[])))))))) :: [])))), (USeq ((USeq
      ((UWrite (P0, Coq_instr_count, (UBinop ((PrimUntyped.UBits2
      PrimUntyped.UPlus), (URead (P0, Coq_instr_count)), (USugar (UConstBits
      ((Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))))))))))))))))))))))))))),
      (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))))))))))))))))))))))))))))))) 1)))))))), (UIf
      ((USugar (UCallModule ((Obj.magic finite_reg0), (Obj.magic id),
      (Obj.magic lift_empty), (Obj.magic isMemoryInst), ((UVar
      ('d'::('I'::('n'::('s'::('t'::[])))))) :: [])))), (UBind
      (('r'::('e'::('s'::('p'::[])))), (USugar (UCallModule
      ((Obj.magic MemResp.coq_FiniteType_reg_t),
      (Obj.magic (fun x -> Coq_fromDMem x)), (Obj.magic lift_empty),
      (Obj.magic MemResp.deq), []))), (UBind
      (('m'::('e'::('m'::('_'::('d'::('a'::('t'::('a'::[])))))))), (UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('d'::('a'::('t'::('a'::[])))))), (UVar
      ('r'::('e'::('s'::('p'::[]))))))), (USeq ((UAssign
      (('m'::('e'::('m'::('_'::('d'::('a'::('t'::('a'::[])))))))), (UBinop
      ((PrimUntyped.UBits2 PrimUntyped.ULsr), (UVar
      ('m'::('e'::('m'::('_'::('d'::('a'::('t'::('a'::[]))))))))), (UBinop
      ((PrimUntyped.UBits2 PrimUntyped.UConcat), (UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('o'::('f'::('f'::('s'::('e'::('t'::[])))))))), (UVar
      ('e'::('x'::('e'::('c'::('u'::('t'::('e'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[])))))))))))))))))))))),
      (USugar (UConstBits ((Pervasives.succ (Pervasives.succ (Pervasives.succ
      0))),
      (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
        (vect_cons (Pervasives.succ 0) false (Obj.magic vect_cons 0 false __)))))))))))),
      (UBind
      (('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[])))))))))))))))))))))))),
      (UBinop ((PrimUntyped.UBits2 PrimUntyped.UConcat), (UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('i'::('s'::('U'::('n'::('s'::('i'::('g'::('n'::('e'::('d'::[])))))))))))),
      (UVar
      ('e'::('x'::('e'::('c'::('u'::('t'::('e'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[])))))))))))))))))))))),
      (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('s'::('i'::('z'::('e'::[])))))), (UVar
      ('e'::('x'::('e'::('c'::('u'::('t'::('e'::('_'::('b'::('o'::('o'::('k'::('k'::('e'::('e'::('p'::('i'::('n'::('g'::[])))))))))))))))))))))))),
      (USugar (USwitch ((UVar
      ('_'::('_'::('r'::('e'::('s'::('e'::('r'::('v'::('e'::('d'::('_'::('_'::('m'::('a'::('t'::('c'::('h'::('P'::('a'::('t'::('t'::('e'::('r'::('n'::[]))))))))))))))))))))))))),
      (UFail (Bits_t 0)),
      (app (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0))),
        (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
          (vect_cons (Pervasives.succ 0) false
            (Obj.magic vect_cons 0 false __)))))), (UAssign
        (('d'::('a'::('t'::('a'::[])))), (USugar (UCallModule
        ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic lift_empty),
        (Obj.magic signExtend (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ 0)))))))) (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ
          0))))))))))))))))))))))))), ((UBinop ((PrimUntyped.UBits2
        (PrimUntyped.UIndexedSlice (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ 0)))))))))), (UVar
        ('m'::('e'::('m'::('_'::('d'::('a'::('t'::('a'::[]))))))))), (USugar
        (UConstBits ((Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ 0))))),
        (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ 0))))) 0)))))) :: []))))))) :: [])
        (app (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0))),
          (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
            (vect_cons (Pervasives.succ 0) false
              (Obj.magic vect_cons 0 false __)))))), (UAssign
          (('d'::('a'::('t'::('a'::[])))), (USugar (UCallModule
          ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic lift_empty),
          (Obj.magic signExtend (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ 0))))))))))))))))
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ 0))))))))))))))))), ((UBinop
          ((PrimUntyped.UBits2 (PrimUntyped.UIndexedSlice (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ
          0)))))))))))))))))), (UVar
          ('m'::('e'::('m'::('_'::('d'::('a'::('t'::('a'::[]))))))))),
          (USugar (UConstBits ((Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
          (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ 0))))) 0)))))) :: []))))))) :: [])
          (app (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
            (Pervasives.succ 0))),
            (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) false
              (vect_cons (Pervasives.succ 0) false
                (Obj.magic vect_cons 0 true __)))))), (UAssign
            (('d'::('a'::('t'::('a'::[])))), (UUnop ((PrimUntyped.UBits1
            (PrimUntyped.UZExtL (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            0)))))))))))))))))))))))))))))))))), (UBinop ((PrimUntyped.UBits2
            (PrimUntyped.UIndexedSlice (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))),
            (UVar
            ('m'::('e'::('m'::('_'::('d'::('a'::('t'::('a'::[]))))))))),
            (USugar (UConstBits ((Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
            (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ 0))))) 0))))))))))) :: [])
            (app (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
              (Pervasives.succ 0))),
              (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0)) true
                (vect_cons (Pervasives.succ 0) false
                  (Obj.magic vect_cons 0 true __)))))), (UAssign
              (('d'::('a'::('t'::('a'::[])))), (UUnop ((PrimUntyped.UBits1
              (PrimUntyped.UZExtL (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              0)))))))))))))))))))))))))))))))))), (UBinop
              ((PrimUntyped.UBits2 (PrimUntyped.UIndexedSlice
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ 0)))))))))))))))))), (UVar
              ('m'::('e'::('m'::('_'::('d'::('a'::('t'::('a'::[]))))))))),
              (USugar (UConstBits ((Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
              (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ 0))))) 0))))))))))) :: [])
              (((USugar (UConstBits ((Pervasives.succ (Pervasives.succ
              (Pervasives.succ 0))),
              (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ 0))
                false
                (vect_cons (Pervasives.succ 0) true
                  (Obj.magic vect_cons 0 false __)))))), (UAssign
              (('d'::('a'::('t'::('a'::[])))), (UVar
              ('m'::('e'::('m'::('_'::('d'::('a'::('t'::('a'::[])))))))))))) :: [])))))))))))))))),
      (USugar (UConstBits (0, (Obj.magic __)))))))), (UIf ((UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('v'::('a'::('l'::('i'::('d'::('_'::('r'::('d'::[])))))))))), (UVar
      ('d'::('I'::('n'::('s'::('t'::[])))))))), (UBind
      (('r'::('d'::('_'::('i'::('d'::('x'::[])))))), (UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField ('r'::('d'::[])))), (UVar
      ('f'::('i'::('e'::('l'::('d'::('s'::[]))))))))), (USeq ((USugar
      (UCallModule ((Obj.magic Scoreboard.finite_reg),
      (Obj.magic (fun x -> Coq_scoreboard x)), (Obj.magic lift_empty),
      (Obj.magic Scoreboard.remove), ((USugar (UCallModule
      ((Obj.magic finite_reg0), (Obj.magic id), (Obj.magic lift_empty),
      (Obj.magic sliceReg), ((UVar
      ('r'::('d'::('_'::('i'::('d'::('x'::[]))))))) :: [])))) :: [])))), (UIf
      ((UBinop ((PrimUntyped.UEq false), (UVar
      ('r'::('d'::('_'::('i'::('d'::('x'::[]))))))), (USugar (UConstBits
      ((Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))),
      (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ 0))))) 0)))))), (USugar (UConstBits
      (0, (Obj.magic __)))), (USugar (UCallModule
      ((Obj.magic Rf.finite_rf_reg), (Obj.magic (fun x -> Coq_rf x)),
      (Obj.magic lift_empty), (Obj.magic Rf.write_0),
      (app ((USugar (UCallModule ((Obj.magic finite_reg0), (Obj.magic id),
        (Obj.magic lift_empty), (Obj.magic sliceReg), ((UVar
        ('r'::('d'::('_'::('i'::('d'::('x'::[]))))))) :: [])))) :: []) ((UVar
        ('d'::('a'::('t'::('a'::[]))))) :: []))))))))))), (USugar (UConstBits
      (0, (Obj.magic __)))))))))))))))))

  (** val coq_MMIO_UART_ADDRESS :
      (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
      (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
      (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
      (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t **)

  let coq_MMIO_UART_ADDRESS =
    Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0))))))))))))))))))))))))))))))) false
      (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0)))))))))))))))))))))))))))))) false
        (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ
          0))))))))))))))))))))))))))))) false
          (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ 0)))))))))))))))))))))))))))) false
            (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ 0))))))))))))))))))))))))))) false
              (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ 0))))))))))))))))))))))))))
                false
                (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ
                  0))))))))))))))))))))))))) false
                  (vect_cons (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ 0)))))))))))))))))))))))) false
                    (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      0))))))))))))))))))))))) false
                      (vect_cons (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ
                        0)))))))))))))))))))))) false
                        (Obj.magic vect_cons (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ
                          0))))))))))))))))))))) false
                          (vect_cons (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            0)))))))))))))))))))) false
                            (Obj.magic vect_cons (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              0))))))))))))))))))) false
                              (vect_cons (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                0)))))))))))))))))) false
                                (Obj.magic vect_cons (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  0))))))))))))))))) false
                                  (vect_cons (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ 0)))))))))))))))) false
                                    (Obj.magic vect_cons (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      0))))))))))))))) false
                                      (vect_cons (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ 0))))))))))))))
                                        false
                                        (Obj.magic vect_cons (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          0))))))))))))) false
                                          (vect_cons (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ 0))))))))))))
                                            false
                                            (Obj.magic vect_cons
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ 0)))))))))))
                                              false
                                              (vect_cons (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ 0))))))))))
                                                false
                                                (Obj.magic vect_cons
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ 0)))))))))
                                                  false
                                                  (vect_cons (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    0)))))))) false
                                                    (Obj.magic vect_cons
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      0))))))) false
                                                      (vect_cons
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        0)))))) false
                                                        (Obj.magic vect_cons
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          0))))) false
                                                          (vect_cons
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            0)))) false
                                                            (Obj.magic
                                                              vect_cons
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              0))) false
                                                              (vect_cons
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                0)) false
                                                                (Obj.magic
                                                                  vect_cons
                                                                  (Pervasives.succ
                                                                  0) true
                                                                  (vect_cons
                                                                    0 false
                                                                    (Obj.magic
                                                                    __))))))))))))))))))))))))))))))))

  (** val coq_MMIO_LED_ADDRESS :
      (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
      (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
      (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
      (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t **)

  let coq_MMIO_LED_ADDRESS =
    Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0))))))))))))))))))))))))))))))) false
      (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0)))))))))))))))))))))))))))))) false
        (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ
          0))))))))))))))))))))))))))))) true
          (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ 0)))))))))))))))))))))))))))) false
            (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ 0))))))))))))))))))))))))))) false
              (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ 0))))))))))))))))))))))))))
                false
                (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ
                  0))))))))))))))))))))))))) false
                  (vect_cons (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ 0)))))))))))))))))))))))) false
                    (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      0))))))))))))))))))))))) false
                      (vect_cons (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ
                        0)))))))))))))))))))))) false
                        (Obj.magic vect_cons (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ
                          0))))))))))))))))))))) false
                          (vect_cons (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            0)))))))))))))))))))) false
                            (Obj.magic vect_cons (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              0))))))))))))))))))) false
                              (vect_cons (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                0)))))))))))))))))) false
                                (Obj.magic vect_cons (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  0))))))))))))))))) false
                                  (vect_cons (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ 0)))))))))))))))) false
                                    (Obj.magic vect_cons (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      0))))))))))))))) false
                                      (vect_cons (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ 0))))))))))))))
                                        false
                                        (Obj.magic vect_cons (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          0))))))))))))) false
                                          (vect_cons (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ 0))))))))))))
                                            false
                                            (Obj.magic vect_cons
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ 0)))))))))))
                                              false
                                              (vect_cons (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ 0))))))))))
                                                false
                                                (Obj.magic vect_cons
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ 0)))))))))
                                                  false
                                                  (vect_cons (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    0)))))))) false
                                                    (Obj.magic vect_cons
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      0))))))) false
                                                      (vect_cons
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        0)))))) false
                                                        (Obj.magic vect_cons
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          0))))) false
                                                          (vect_cons
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            0)))) false
                                                            (Obj.magic
                                                              vect_cons
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              0))) false
                                                              (vect_cons
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                0)) false
                                                                (Obj.magic
                                                                  vect_cons
                                                                  (Pervasives.succ
                                                                  0) true
                                                                  (vect_cons
                                                                    0 false
                                                                    (Obj.magic
                                                                    __))))))))))))))))))))))))))))))))

  (** val coq_MMIO_EXIT_ADDRESS :
      (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
      (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
      (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
      (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t **)

  let coq_MMIO_EXIT_ADDRESS =
    Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0))))))))))))))))))))))))))))))) false
      (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0)))))))))))))))))))))))))))))) false
        (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ
          0))))))))))))))))))))))))))))) false
          (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ 0)))))))))))))))))))))))))))) false
            (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ 0))))))))))))))))))))))))))) false
              (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ 0))))))))))))))))))))))))))
                false
                (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ
                  0))))))))))))))))))))))))) false
                  (vect_cons (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ 0)))))))))))))))))))))))) false
                    (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      0))))))))))))))))))))))) false
                      (vect_cons (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ
                        0)))))))))))))))))))))) false
                        (Obj.magic vect_cons (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ
                          0))))))))))))))))))))) false
                          (vect_cons (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            0)))))))))))))))))))) false
                            (Obj.magic vect_cons (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              0))))))))))))))))))) true
                              (vect_cons (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                0)))))))))))))))))) false
                                (Obj.magic vect_cons (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  0))))))))))))))))) false
                                  (vect_cons (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ 0)))))))))))))))) false
                                    (Obj.magic vect_cons (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      0))))))))))))))) false
                                      (vect_cons (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ 0))))))))))))))
                                        false
                                        (Obj.magic vect_cons (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          0))))))))))))) false
                                          (vect_cons (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ 0))))))))))))
                                            false
                                            (Obj.magic vect_cons
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ 0)))))))))))
                                              false
                                              (vect_cons (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ 0))))))))))
                                                false
                                                (Obj.magic vect_cons
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ 0)))))))))
                                                  false
                                                  (vect_cons (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    0)))))))) false
                                                    (Obj.magic vect_cons
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      0))))))) false
                                                      (vect_cons
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        0)))))) false
                                                        (Obj.magic vect_cons
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          0))))) false
                                                          (vect_cons
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            0)))) false
                                                            (Obj.magic
                                                              vect_cons
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              0))) false
                                                              (vect_cons
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                0)) false
                                                                (Obj.magic
                                                                  vect_cons
                                                                  (Pervasives.succ
                                                                  0) true
                                                                  (vect_cons
                                                                    0 false
                                                                    (Obj.magic
                                                                    __))))))))))))))))))))))))))))))))

  (** val coq_MMIO_HOST_ID_ADDRESS :
      (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
      (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
      (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool, (bool,
      (bool, (bool, __) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t) vect_cons_t)
      vect_cons_t) vect_cons_t) vect_cons_t **)

  let coq_MMIO_HOST_ID_ADDRESS =
    Obj.magic vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0))))))))))))))))))))))))))))))) false
      (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0)))))))))))))))))))))))))))))) false
        (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ
          0))))))))))))))))))))))))))))) true
          (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ 0)))))))))))))))))))))))))))) false
            (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ 0))))))))))))))))))))))))))) false
              (vect_cons (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ 0))))))))))))))))))))))))))
                false
                (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ
                  0))))))))))))))))))))))))) false
                  (vect_cons (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ 0)))))))))))))))))))))))) false
                    (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      0))))))))))))))))))))))) false
                      (vect_cons (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ
                        0)))))))))))))))))))))) false
                        (Obj.magic vect_cons (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ (Pervasives.succ
                          0))))))))))))))))))))) false
                          (vect_cons (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            0)))))))))))))))))))) false
                            (Obj.magic vect_cons (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              0))))))))))))))))))) true
                              (vect_cons (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                0)))))))))))))))))) false
                                (Obj.magic vect_cons (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  0))))))))))))))))) false
                                  (vect_cons (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ 0)))))))))))))))) false
                                    (Obj.magic vect_cons (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      0))))))))))))))) false
                                      (vect_cons (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ 0))))))))))))))
                                        false
                                        (Obj.magic vect_cons (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          0))))))))))))) false
                                          (vect_cons (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ 0))))))))))))
                                            false
                                            (Obj.magic vect_cons
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ 0)))))))))))
                                              false
                                              (vect_cons (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ 0))))))))))
                                                false
                                                (Obj.magic vect_cons
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ 0)))))))))
                                                  false
                                                  (vect_cons (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    0)))))))) false
                                                    (Obj.magic vect_cons
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      0))))))) false
                                                      (vect_cons
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        0)))))) false
                                                        (Obj.magic vect_cons
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          0))))) false
                                                          (vect_cons
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            0)))) false
                                                            (Obj.magic
                                                              vect_cons
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              0))) false
                                                              (vect_cons
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                0)) false
                                                                (Obj.magic
                                                                  vect_cons
                                                                  (Pervasives.succ
                                                                  0) true
                                                                  (vect_cons
                                                                    0 false
                                                                    (Obj.magic
                                                                    __))))))))))))))))))))))))))))))))

  (** val memoryBus :
      memory -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, reg_t, ext_fn_t)
      uaction) internalFunction **)

  let memoryBus m =
    { int_name =
      ('m'::('e'::('m'::('o'::('r'::('y'::('B'::('u'::('s'::[])))))))));
      int_argspec =
      (app
        ((prod_of_argsig { arg_name =
           ('g'::('e'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[])))))))));
           arg_type = (Bits_t (Pervasives.succ 0)) }) :: [])
        (app
          ((prod_of_argsig { arg_name =
             ('p'::('u'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[])))))))));
             arg_type = (Bits_t (Pervasives.succ 0)) }) :: [])
          ((prod_of_argsig { arg_name =
             ('p'::('u'::('t'::('_'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[])))))))))));
             arg_type = (Struct_t mem_req) }) :: []))); int_retSig =
      (Struct_t mem_output); int_body =
      (match m with
       | Coq_imem ->
         UExternalCall ((Coq_ext_mem m), (USugar (UStructInit (mem_input,
           (app
             (app
               ((('g'::('e'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[]))))))))),
               (UVar
               ('g'::('e'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[]))))))))))) :: [])
               ((('p'::('u'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[]))))))))),
               (UVar
               ('p'::('u'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[]))))))))))) :: []))
             ((('p'::('u'::('t'::('_'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))))))),
             (UVar
             ('p'::('u'::('t'::('_'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))))))))) :: []))))))
       | Coq_dmem ->
         UBind (('a'::('d'::('d'::('r'::[])))), (UUnop ((PrimUntyped.UStruct1
           (PrimUntyped.UGetField ('a'::('d'::('d'::('r'::[])))))), (UVar
           ('p'::('u'::('t'::('_'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[])))))))))))))),
           (UBind (('b'::('y'::('t'::('e'::('_'::('e'::('n'::[]))))))),
           (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('b'::('y'::('t'::('e'::('_'::('e'::('n'::[]))))))))), (UVar
           ('p'::('u'::('t'::('_'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[])))))))))))))),
           (UBind
           (('i'::('s'::('_'::('w'::('r'::('i'::('t'::('e'::[])))))))),
           (UBinop ((PrimUntyped.UEq false), (UVar
           ('b'::('y'::('t'::('e'::('_'::('e'::('n'::[])))))))), (USugar
           (UConstBits ((Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ 0)))),
           (Obj.magic vect_cons (Pervasives.succ (Pervasives.succ
             (Pervasives.succ 0))) true
             (vect_cons (Pervasives.succ (Pervasives.succ 0)) true
               (Obj.magic vect_cons (Pervasives.succ 0) true
                 (vect_cons 0 true (Obj.magic __)))))))))), (UBind
           (('i'::('s'::('_'::('u'::('a'::('r'::('t'::[]))))))), (UBinop
           ((PrimUntyped.UEq false), (UVar ('a'::('d'::('d'::('r'::[]))))),
           (USugar (UConstBits ((Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           0)))))))))))))))))))))))))))))))),
           (Obj.magic coq_MMIO_UART_ADDRESS)))))), (UBind
           (('i'::('s'::('_'::('u'::('a'::('r'::('t'::('_'::('r'::('e'::('a'::('d'::[])))))))))))),
           (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
           ('i'::('s'::('_'::('u'::('a'::('r'::('t'::[])))))))), (UUnop
           ((PrimUntyped.UBits1 PrimUntyped.UNot), (UVar
           ('i'::('s'::('_'::('w'::('r'::('i'::('t'::('e'::[]))))))))))))),
           (UBind
           (('i'::('s'::('_'::('u'::('a'::('r'::('t'::('_'::('w'::('r'::('i'::('t'::('e'::[]))))))))))))),
           (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
           ('i'::('s'::('_'::('u'::('a'::('r'::('t'::[])))))))), (UVar
           ('i'::('s'::('_'::('w'::('r'::('i'::('t'::('e'::[]))))))))))),
           (UBind (('i'::('s'::('_'::('l'::('e'::('d'::[])))))), (UBinop
           ((PrimUntyped.UEq false), (UVar ('a'::('d'::('d'::('r'::[]))))),
           (USugar (UConstBits ((Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           0)))))))))))))))))))))))))))))))),
           (Obj.magic coq_MMIO_LED_ADDRESS)))))), (UBind
           (('i'::('s'::('_'::('l'::('e'::('d'::('_'::('w'::('r'::('i'::('t'::('e'::[])))))))))))),
           (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
           ('i'::('s'::('_'::('l'::('e'::('d'::[]))))))), (UVar
           ('i'::('s'::('_'::('w'::('r'::('i'::('t'::('e'::[]))))))))))),
           (UBind
           (('i'::('s'::('_'::('f'::('i'::('n'::('i'::('s'::('h'::[]))))))))),
           (UBinop ((PrimUntyped.UEq false), (UVar
           ('a'::('d'::('d'::('r'::[]))))), (USugar (UConstBits
           ((Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ
           0)))))))))))))))))))))))))))))))),
           (Obj.magic coq_MMIO_EXIT_ADDRESS)))))), (UBind
           (('i'::('s'::('_'::('f'::('i'::('n'::('i'::('s'::('h'::('_'::('w'::('r'::('i'::('t'::('e'::[]))))))))))))))),
           (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
           ('i'::('s'::('_'::('f'::('i'::('n'::('i'::('s'::('h'::[])))))))))),
           (UVar
           ('i'::('s'::('_'::('w'::('r'::('i'::('t'::('e'::[]))))))))))),
           (UBind
           (('i'::('s'::('_'::('h'::('o'::('s'::('t'::('_'::('i'::('d'::[])))))))))),
           (UBinop ((PrimUntyped.UEq false), (UVar
           ('a'::('d'::('d'::('r'::[]))))), (USugar (UConstBits
           ((Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ
           0)))))))))))))))))))))))))))))))),
           (Obj.magic coq_MMIO_HOST_ID_ADDRESS)))))), (UBind
           (('i'::('s'::('_'::('h'::('o'::('s'::('t'::('_'::('i'::('d'::('_'::('r'::('e'::('a'::('d'::[]))))))))))))))),
           (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
           ('i'::('s'::('_'::('h'::('o'::('s'::('t'::('_'::('i'::('d'::[]))))))))))),
           (UUnop ((PrimUntyped.UBits1 PrimUntyped.UNot), (UVar
           ('i'::('s'::('_'::('w'::('r'::('i'::('t'::('e'::[]))))))))))))),
           (UBind (('i'::('s'::('_'::('m'::('e'::('m'::[])))))), (UBinop
           ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UUnop
           ((PrimUntyped.UBits1 PrimUntyped.UNot), (UVar
           ('i'::('s'::('_'::('u'::('a'::('r'::('t'::[])))))))))), (UBinop
           ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UUnop
           ((PrimUntyped.UBits1 PrimUntyped.UNot), (UVar
           ('i'::('s'::('_'::('l'::('e'::('d'::[]))))))))), (UBinop
           ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UUnop
           ((PrimUntyped.UBits1 PrimUntyped.UNot), (UVar
           ('i'::('s'::('_'::('f'::('i'::('n'::('i'::('s'::('h'::[])))))))))))),
           (UUnop ((PrimUntyped.UBits1 PrimUntyped.UNot), (UVar
           ('i'::('s'::('_'::('h'::('o'::('s'::('t'::('_'::('i'::('d'::[]))))))))))))))))))),
           (UIf ((UVar
           ('i'::('s'::('_'::('u'::('a'::('r'::('t'::('_'::('w'::('r'::('i'::('t'::('e'::[])))))))))))))),
           (UBind (('c'::('h'::('a'::('r'::[])))), (UBinop
           ((PrimUntyped.UBits2 (PrimUntyped.UIndexedSlice (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ 0)))))))))), (UUnop ((PrimUntyped.UStruct1
           (PrimUntyped.UGetField ('d'::('a'::('t'::('a'::[])))))), (UVar
           ('p'::('u'::('t'::('_'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[])))))))))))))),
           (USugar (UConstBits ((Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
           (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ 0))))) 0)))))), (UBind
           (('m'::('a'::('y'::('_'::('r'::('u'::('n'::[]))))))), (UBinop
           ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
           ('g'::('e'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[])))))))))),
           (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
           ('p'::('u'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[])))))))))),
           (UVar
           ('i'::('s'::('_'::('u'::('a'::('r'::('t'::('_'::('w'::('r'::('i'::('t'::('e'::[])))))))))))))))))),
           (UBind (('r'::('e'::('a'::('d'::('y'::[]))))), (UExternalCall
           (Coq_ext_uart_write, (USugar (UStructInit
           ((maybe (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ 0)))))))))),
           (app ((('v'::('a'::('l'::('i'::('d'::[]))))), (UVar
             ('m'::('a'::('y'::('_'::('r'::('u'::('n'::[]))))))))) :: [])
             ((('d'::('a'::('t'::('a'::[])))), (UVar
             ('c'::('h'::('a'::('r'::[])))))) :: []))))))), (USugar
           (UStructInit (mem_output,
           (app
             (app
               ((('g'::('e'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[]))))))))),
               (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
               ('m'::('a'::('y'::('_'::('r'::('u'::('n'::[])))))))), (UVar
               ('r'::('e'::('a'::('d'::('y'::[]))))))))) :: [])
               ((('p'::('u'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[]))))))))),
               (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
               ('m'::('a'::('y'::('_'::('r'::('u'::('n'::[])))))))), (UVar
               ('r'::('e'::('a'::('d'::('y'::[]))))))))) :: []))
             ((('g'::('e'::('t'::('_'::('r'::('e'::('s'::('p'::('o'::('n'::('s'::('e'::[])))))))))))),
             (USugar (UStructInit (mem_resp,
             (app
               (app ((('b'::('y'::('t'::('e'::('_'::('e'::('n'::[]))))))),
                 (UVar
                 ('b'::('y'::('t'::('e'::('_'::('e'::('n'::[]))))))))) :: [])
                 ((('a'::('d'::('d'::('r'::[])))), (UVar
                 ('a'::('d'::('d'::('r'::[])))))) :: []))
               ((('d'::('a'::('t'::('a'::[])))), (USugar (UConstBits
               ((Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ
               0)))))))))))))))))))))))))))))))),
               (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ
                 0)))))))))))))))))))))))))))))))) 0))))) :: [])))))) :: []))))))))))),
           (UIf ((UVar
           ('i'::('s'::('_'::('u'::('a'::('r'::('t'::('_'::('r'::('e'::('a'::('d'::[]))))))))))))),
           (UBind (('m'::('a'::('y'::('_'::('r'::('u'::('n'::[]))))))),
           (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
           ('g'::('e'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[])))))))))),
           (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
           ('p'::('u'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[])))))))))),
           (UVar
           ('i'::('s'::('_'::('u'::('a'::('r'::('t'::('_'::('r'::('e'::('a'::('d'::[]))))))))))))))))),
           (UBind
           (('o'::('p'::('t'::('_'::('c'::('h'::('a'::('r'::[])))))))),
           (UExternalCall (Coq_ext_uart_read, (UVar
           ('m'::('a'::('y'::('_'::('r'::('u'::('n'::[])))))))))), (UBind
           (('r'::('e'::('a'::('d'::('y'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('v'::('a'::('l'::('i'::('d'::[]))))))), (UVar
           ('o'::('p'::('t'::('_'::('c'::('h'::('a'::('r'::[]))))))))))),
           (USugar (UStructInit (mem_output,
           (app
             (app
               ((('g'::('e'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[]))))))))),
               (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
               ('m'::('a'::('y'::('_'::('r'::('u'::('n'::[])))))))), (UVar
               ('r'::('e'::('a'::('d'::('y'::[]))))))))) :: [])
               ((('p'::('u'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[]))))))))),
               (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
               ('m'::('a'::('y'::('_'::('r'::('u'::('n'::[])))))))), (UVar
               ('r'::('e'::('a'::('d'::('y'::[]))))))))) :: []))
             ((('g'::('e'::('t'::('_'::('r'::('e'::('s'::('p'::('o'::('n'::('s'::('e'::[])))))))))))),
             (USugar (UStructInit (mem_resp,
             (app
               (app ((('b'::('y'::('t'::('e'::('_'::('e'::('n'::[]))))))),
                 (UVar
                 ('b'::('y'::('t'::('e'::('_'::('e'::('n'::[]))))))))) :: [])
                 ((('a'::('d'::('d'::('r'::[])))), (UVar
                 ('a'::('d'::('d'::('r'::[])))))) :: []))
               ((('d'::('a'::('t'::('a'::[])))), (UUnop ((PrimUntyped.UBits1
               (PrimUntyped.UZExtL (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               0)))))))))))))))))))))))))))))))))), (UUnop
               ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
               ('d'::('a'::('t'::('a'::[])))))), (UVar
               ('o'::('p'::('t'::('_'::('c'::('h'::('a'::('r'::[])))))))))))))) :: [])))))) :: []))))))))))),
           (UIf ((UVar ('i'::('s'::('_'::('l'::('e'::('d'::[]))))))), (UBind
           (('o'::('n'::[])), (UBinop ((PrimUntyped.UBits2 PrimUntyped.USel),
           (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('d'::('a'::('t'::('a'::[])))))), (UVar
           ('p'::('u'::('t'::('_'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[])))))))))))))),
           (USugar (UConstBits ((Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
           (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ 0))))) 0)))))), (UBind
           (('m'::('a'::('y'::('_'::('r'::('u'::('n'::[]))))))), (UBinop
           ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
           ('g'::('e'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[])))))))))),
           (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
           ('p'::('u'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[])))))))))),
           (UVar
           ('i'::('s'::('_'::('l'::('e'::('d'::('_'::('w'::('r'::('i'::('t'::('e'::[]))))))))))))))))),
           (UBind (('c'::('u'::('r'::('r'::('e'::('n'::('t'::[]))))))),
           (UExternalCall (Coq_ext_led, (USugar (UStructInit
           ((maybe (Bits_t (Pervasives.succ 0))),
           (app ((('v'::('a'::('l'::('i'::('d'::[]))))), (UVar
             ('m'::('a'::('y'::('_'::('r'::('u'::('n'::[]))))))))) :: [])
             ((('d'::('a'::('t'::('a'::[])))), (UVar
             ('o'::('n'::[])))) :: []))))))), (UBind
           (('r'::('e'::('a'::('d'::('y'::[]))))), (USugar (UConstBits
           ((Pervasives.succ 0), (Obj.magic vect_cons 0 true __)))), (USugar
           (UStructInit (mem_output,
           (app
             (app
               ((('g'::('e'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[]))))))))),
               (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
               ('m'::('a'::('y'::('_'::('r'::('u'::('n'::[])))))))), (UVar
               ('r'::('e'::('a'::('d'::('y'::[]))))))))) :: [])
               ((('p'::('u'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[]))))))))),
               (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
               ('m'::('a'::('y'::('_'::('r'::('u'::('n'::[])))))))), (UVar
               ('r'::('e'::('a'::('d'::('y'::[]))))))))) :: []))
             ((('g'::('e'::('t'::('_'::('r'::('e'::('s'::('p'::('o'::('n'::('s'::('e'::[])))))))))))),
             (USugar (UStructInit (mem_resp,
             (app
               (app ((('b'::('y'::('t'::('e'::('_'::('e'::('n'::[]))))))),
                 (UVar
                 ('b'::('y'::('t'::('e'::('_'::('e'::('n'::[]))))))))) :: [])
                 ((('a'::('d'::('d'::('r'::[])))), (UVar
                 ('a'::('d'::('d'::('r'::[])))))) :: []))
               ((('d'::('a'::('t'::('a'::[])))), (UUnop ((PrimUntyped.UBits1
               (PrimUntyped.UZExtL (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               0)))))))))))))))))))))))))))))))))), (UVar
               ('c'::('u'::('r'::('r'::('e'::('n'::('t'::[]))))))))))) :: [])))))) :: []))))))))))))),
           (UIf ((UVar
           ('i'::('s'::('_'::('f'::('i'::('n'::('i'::('s'::('h'::[])))))))))),
           (UBind (('c'::('h'::('a'::('r'::[])))), (UBinop
           ((PrimUntyped.UBits2 (PrimUntyped.UIndexedSlice (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ 0)))))))))), (UUnop ((PrimUntyped.UStruct1
           (PrimUntyped.UGetField ('d'::('a'::('t'::('a'::[])))))), (UVar
           ('p'::('u'::('t'::('_'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[])))))))))))))),
           (USugar (UConstBits ((Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
           (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ 0))))) 0)))))), (UBind
           (('m'::('a'::('y'::('_'::('r'::('u'::('n'::[]))))))), (UBinop
           ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
           ('g'::('e'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[])))))))))),
           (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
           ('p'::('u'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[])))))))))),
           (UVar
           ('i'::('s'::('_'::('f'::('i'::('n'::('i'::('s'::('h'::('_'::('w'::('r'::('i'::('t'::('e'::[])))))))))))))))))))),
           (UBind
           (('r'::('e'::('s'::('p'::('o'::('n'::('s'::('e'::[])))))))),
           (UExternalCall (Coq_ext_finish, (USugar (UStructInit
           ((maybe (Bits_t (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ 0)))))))))),
           (app ((('v'::('a'::('l'::('i'::('d'::[]))))), (UVar
             ('m'::('a'::('y'::('_'::('r'::('u'::('n'::[]))))))))) :: [])
             ((('d'::('a'::('t'::('a'::[])))), (UVar
             ('c'::('h'::('a'::('r'::[])))))) :: []))))))), (UBind
           (('r'::('e'::('a'::('d'::('y'::[]))))), (USugar (UConstBits
           ((Pervasives.succ 0), (Obj.magic vect_cons 0 true __)))), (USugar
           (UStructInit (mem_output,
           (app
             (app
               ((('g'::('e'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[]))))))))),
               (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
               ('m'::('a'::('y'::('_'::('r'::('u'::('n'::[])))))))), (UVar
               ('r'::('e'::('a'::('d'::('y'::[]))))))))) :: [])
               ((('p'::('u'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[]))))))))),
               (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
               ('m'::('a'::('y'::('_'::('r'::('u'::('n'::[])))))))), (UVar
               ('r'::('e'::('a'::('d'::('y'::[]))))))))) :: []))
             ((('g'::('e'::('t'::('_'::('r'::('e'::('s'::('p'::('o'::('n'::('s'::('e'::[])))))))))))),
             (USugar (UStructInit (mem_resp,
             (app
               (app ((('b'::('y'::('t'::('e'::('_'::('e'::('n'::[]))))))),
                 (UVar
                 ('b'::('y'::('t'::('e'::('_'::('e'::('n'::[]))))))))) :: [])
                 ((('a'::('d'::('d'::('r'::[])))), (UVar
                 ('a'::('d'::('d'::('r'::[])))))) :: []))
               ((('d'::('a'::('t'::('a'::[])))), (UUnop ((PrimUntyped.UBits1
               (PrimUntyped.UZExtL (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               0)))))))))))))))))))))))))))))))))), (UVar
               ('r'::('e'::('s'::('p'::('o'::('n'::('s'::('e'::[])))))))))))) :: [])))))) :: []))))))))))))),
           (UIf ((UVar
           ('i'::('s'::('_'::('h'::('o'::('s'::('t'::('_'::('i'::('d'::[]))))))))))),
           (UBind (('m'::('a'::('y'::('_'::('r'::('u'::('n'::[]))))))),
           (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
           ('g'::('e'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[])))))))))),
           (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
           ('p'::('u'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[])))))))))),
           (UVar
           ('i'::('s'::('_'::('h'::('o'::('s'::('t'::('_'::('i'::('d'::('_'::('r'::('e'::('a'::('d'::[])))))))))))))))))))),
           (UBind
           (('r'::('e'::('s'::('p'::('o'::('n'::('s'::('e'::[])))))))),
           (UUnop ((PrimUntyped.UConv PrimUntyped.UPack), (UExternalCall
           (Coq_ext_host_id, (USugar (UConstBits ((Pervasives.succ 0),
           (Obj.magic vect_cons 0 true __)))))))), (UBind
           (('r'::('e'::('a'::('d'::('y'::[]))))), (USugar (UConstBits
           ((Pervasives.succ 0), (Obj.magic vect_cons 0 true __)))), (USugar
           (UStructInit (mem_output,
           (app
             (app
               ((('g'::('e'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[]))))))))),
               (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
               ('m'::('a'::('y'::('_'::('r'::('u'::('n'::[])))))))), (UVar
               ('r'::('e'::('a'::('d'::('y'::[]))))))))) :: [])
               ((('p'::('u'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[]))))))))),
               (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
               ('m'::('a'::('y'::('_'::('r'::('u'::('n'::[])))))))), (UVar
               ('r'::('e'::('a'::('d'::('y'::[]))))))))) :: []))
             ((('g'::('e'::('t'::('_'::('r'::('e'::('s'::('p'::('o'::('n'::('s'::('e'::[])))))))))))),
             (USugar (UStructInit (mem_resp,
             (app
               (app ((('b'::('y'::('t'::('e'::('_'::('e'::('n'::[]))))))),
                 (UVar
                 ('b'::('y'::('t'::('e'::('_'::('e'::('n'::[]))))))))) :: [])
                 ((('a'::('d'::('d'::('r'::[])))), (UVar
                 ('a'::('d'::('d'::('r'::[])))))) :: []))
               ((('d'::('a'::('t'::('a'::[])))), (UUnop ((PrimUntyped.UBits1
               (PrimUntyped.UZExtL (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               0)))))))))))))))))))))))))))))))))), (UVar
               ('r'::('e'::('s'::('p'::('o'::('n'::('s'::('e'::[])))))))))))) :: [])))))) :: []))))))))))),
           (UExternalCall ((Coq_ext_mem m), (USugar (UStructInit (mem_input,
           (app
             (app
               ((('g'::('e'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[]))))))))),
               (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
               ('g'::('e'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[])))))))))),
               (UVar ('i'::('s'::('_'::('m'::('e'::('m'::[])))))))))) :: [])
               ((('p'::('u'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[]))))))))),
               (UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
               ('p'::('u'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[])))))))))),
               (UVar ('i'::('s'::('_'::('m'::('e'::('m'::[])))))))))) :: []))
             ((('p'::('u'::('t'::('_'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))))))),
             (UVar
             ('p'::('u'::('t'::('_'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))))))))) :: []))))))))))))))))))))))))))))))))))))))))))) }

  (** val mem :
      memory -> reg_t finiteType -> ShadowStack.reg_t finiteType -> (pos_t,
      var_t, fn_name_t, reg_t, ext_fn_t) uaction **)

  let mem m finite_reg0 _ =
    let fromMem = fun x ->
      match m with
      | Coq_imem -> Coq_fromIMem x
      | Coq_dmem -> Coq_fromDMem x
    in
    let toMem = fun x ->
      match m with
      | Coq_imem -> Coq_toIMem x
      | Coq_dmem -> Coq_toDMem x
    in
    USeq ((UIf ((UBinop ((PrimUntyped.UEq false), (URead (P0, Coq_halt)),
    (USugar (UConstBits ((Pervasives.succ 0),
    (Obj.magic vect_cons 0 true __)))))), (UFail (Bits_t 0)), (USugar
    (UConstBits (0, (Obj.magic __)))))), (UBind
    (('g'::('e'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[]))))))))),
    (USugar (UCallModule ((Obj.magic MemResp.coq_FiniteType_reg_t),
    (Obj.magic fromMem), (Obj.magic lift_empty), (Obj.magic MemResp.can_enq),
    []))), (UBind
    (('p'::('u'::('t'::('_'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::('_'::('o'::('p'::('t'::[]))))))))))))))),
    (USugar (UCallModule ((Obj.magic MemReq.coq_FiniteType_reg_t),
    (Obj.magic toMem), (Obj.magic lift_empty), (Obj.magic MemReq.peek),
    []))), (UBind
    (('p'::('u'::('t'::('_'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))))))),
    (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
    ('d'::('a'::('t'::('a'::[])))))), (UVar
    ('p'::('u'::('t'::('_'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::('_'::('o'::('p'::('t'::[])))))))))))))))))),
    (UBind
    (('p'::('u'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[]))))))))),
    (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
    ('v'::('a'::('l'::('i'::('d'::[]))))))), (UVar
    ('p'::('u'::('t'::('_'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::('_'::('o'::('p'::('t'::[])))))))))))))))))),
    (UBind (('m'::('e'::('m'::('_'::('o'::('u'::('t'::[]))))))), (USugar
    (UCallModule ((Obj.magic finite_reg0), (Obj.magic id),
    (Obj.magic lift_self), (Obj.magic memoryBus m),
    (app ((UVar
      ('g'::('e'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[])))))))))) :: [])
      (app ((UVar
        ('p'::('u'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[])))))))))) :: [])
        ((UVar
        ('p'::('u'::('t'::('_'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[])))))))))))) :: [])))))),
    (USeq ((UIf ((UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
    ('g'::('e'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[])))))))))),
    (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
    ('g'::('e'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[]))))))))))),
    (UVar ('m'::('e'::('m'::('_'::('o'::('u'::('t'::[])))))))))))), (USugar
    (UCallModule ((Obj.magic MemResp.coq_FiniteType_reg_t),
    (Obj.magic fromMem), (Obj.magic lift_empty), (Obj.magic MemResp.enq),
    ((UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
    ('g'::('e'::('t'::('_'::('r'::('e'::('s'::('p'::('o'::('n'::('s'::('e'::[])))))))))))))),
    (UVar ('m'::('e'::('m'::('_'::('o'::('u'::('t'::[])))))))))) :: [])))),
    (USugar (UConstBits (0, (Obj.magic __)))))), (UIf ((UBinop
    ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UVar
    ('p'::('u'::('t'::('_'::('v'::('a'::('l'::('i'::('d'::[])))))))))),
    (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
    ('p'::('u'::('t'::('_'::('r'::('e'::('a'::('d'::('y'::[]))))))))))),
    (UVar ('m'::('e'::('m'::('_'::('o'::('u'::('t'::[])))))))))))), (UUnop
    ((PrimUntyped.UConv PrimUntyped.UIgnore), (USugar (UCallModule
    ((Obj.magic MemReq.coq_FiniteType_reg_t), (Obj.magic toMem),
    (Obj.magic lift_empty), (Obj.magic MemReq.deq), []))))), (USugar
    (UConstBits (0, (Obj.magic __)))))))))))))))))))

  (** val tick : (pos_t, var_t, fn_name_t, reg_t, ext_fn_t) uaction **)

  let tick =
    USeq ((UIf ((UBinop ((PrimUntyped.UEq false), (URead (P0, Coq_halt)),
      (USugar (UConstBits ((Pervasives.succ 0),
      (Obj.magic vect_cons 0 true __)))))), (UFail (Bits_t 0)), (USugar
      (UConstBits (0, (Obj.magic __)))))), (UWrite (P0, Coq_cycle_count,
      (UBinop ((PrimUntyped.UBits2 PrimUntyped.UPlus), (URead (P0,
      Coq_cycle_count)), (USugar (UConstBits ((Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))))))))))))))))))))))))))),
      (Bits.of_N (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))))))))))))))))))))))))))))))) 1)))))))))

  (** val coq_Show_reg_t : reg_t show **)

  let coq_Show_reg_t =
    { show0 = (fun h ->
      match h with
      | Coq_toIMem state ->
        't'::('o'::('I'::('M'::('e'::('m'::('_'::(match state with
                                                  | MemReq.Coq_data0 ->
                                                    'd'::('a'::('t'::('a'::('0'::[]))))
                                                  | MemReq.Coq_valid0 ->
                                                    'v'::('a'::('l'::('i'::('d'::('0'::[]))))))))))))
      | Coq_fromIMem state ->
        'f'::('r'::('o'::('m'::('I'::('M'::('e'::('m'::('_'::(match state with
                                                              | MemResp.Coq_data0 ->
                                                                'd'::('a'::('t'::('a'::('0'::[]))))
                                                              | MemResp.Coq_valid0 ->
                                                                'v'::('a'::('l'::('i'::('d'::('0'::[]))))))))))))))
      | Coq_toDMem state ->
        't'::('o'::('D'::('M'::('e'::('m'::('_'::(match state with
                                                  | MemReq.Coq_data0 ->
                                                    'd'::('a'::('t'::('a'::('0'::[]))))
                                                  | MemReq.Coq_valid0 ->
                                                    'v'::('a'::('l'::('i'::('d'::('0'::[]))))))))))))
      | Coq_fromDMem state ->
        'f'::('r'::('o'::('m'::('D'::('M'::('e'::('m'::('_'::(match state with
                                                              | MemResp.Coq_data0 ->
                                                                'd'::('a'::('t'::('a'::('0'::[]))))
                                                              | MemResp.Coq_valid0 ->
                                                                'v'::('a'::('l'::('i'::('d'::('0'::[]))))))))))))))
      | Coq_f2d state ->
        'f'::('2'::('d'::('_'::(match state with
                                | Coq_fromFetch.Coq_data0 ->
                                  'd'::('a'::('t'::('a'::('0'::[]))))
                                | Coq_fromFetch.Coq_valid0 ->
                                  'v'::('a'::('l'::('i'::('d'::('0'::[])))))))))
      | Coq_f2dprim state ->
        'f'::('2'::('d'::('p'::('r'::('i'::('m'::('_'::(match state with
                                                        | Coq_waitFromFetch.Coq_data0 ->
                                                          'd'::('a'::('t'::('a'::('0'::[]))))
                                                        | Coq_waitFromFetch.Coq_valid0 ->
                                                          'v'::('a'::('l'::('i'::('d'::('0'::[])))))))))))))
      | Coq_d2e state ->
        'd'::('2'::('e'::('_'::(match state with
                                | Coq_fromDecode.Coq_data0 ->
                                  'd'::('a'::('t'::('a'::('0'::[]))))
                                | Coq_fromDecode.Coq_valid0 ->
                                  'v'::('a'::('l'::('i'::('d'::('0'::[])))))))))
      | Coq_e2w state ->
        'e'::('2'::('w'::('_'::(match state with
                                | Coq_fromExecute.Coq_data0 ->
                                  'd'::('a'::('t'::('a'::('0'::[]))))
                                | Coq_fromExecute.Coq_valid0 ->
                                  'v'::('a'::('l'::('i'::('d'::('0'::[])))))))))
      | Coq_rf state ->
        'r'::('f'::('_'::(let Rf.Coq_rData n0 = state in
                          'r'::('D'::('a'::('t'::('a'::('_'::(Show_nat.string_of_nat
                                                               ((fun fthisone fanotherone n -> if n = 0 then fthisone () else fanotherone (n - 1))
                                                                  (fun _ ->
                                                                  0)
                                                                  (fun idx ->
                                                                  Pervasives.succ
                                                                  (index_to_nat
                                                                    (pred
                                                                    (Nat.pow
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))
                                                                    RfParams.idx_sz))
                                                                    idx))
                                                                  (Obj.magic
                                                                    n0)))))))))))
      | Coq_stack state ->
        's'::('t'::('a'::('c'::('k'::('_'::(ShadowStack.coq_Show_reg_t.show0
                                             state))))))
      | Coq_scoreboard state ->
        's'::('c'::('o'::('r'::('e'::('b'::('o'::('a'::('r'::('d'::('_'::
          (let Scoreboard.Scores state0 = state in
           'S'::('c'::('o'::('r'::('e'::('s'::('_'::(let Scoreboard.Rf.Coq_rData n0 =
                                                       state0
                                                     in
                                                     'r'::('D'::('a'::('t'::('a'::('_'::
                                                     (Show_nat.string_of_nat
                                                       ((fun fthisone fanotherone n -> if n = 0 then fthisone () else fanotherone (n - 1))
                                                          (fun _ ->
                                                          0)
                                                          (fun idx ->
                                                          Pervasives.succ
                                                          (index_to_nat
                                                            (pred
                                                              (Nat.pow
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                0))
                                                                Scoreboard.RfParams.idx_sz))
                                                            idx))
                                                          (Obj.magic n0))))))))))))))))))))))))))
      | Coq_cycle_count ->
        'c'::('y'::('c'::('l'::('e'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))
      | Coq_instr_count ->
        'i'::('n'::('s'::('t'::('r'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))
      | Coq_pc -> 'p'::('c'::[])
      | Coq_epoch -> 'e'::('p'::('o'::('c'::('h'::[]))))
      | Coq_debug -> 'd'::('e'::('b'::('u'::('g'::[]))))
      | Coq_on_off -> 'o'::('n'::('_'::('o'::('f'::('f'::[])))))
      | Coq_halt -> 'h'::('a'::('l'::('t'::[])))) }

  (** val coq_Show_ext_fn_t : ext_fn_t show **)

  let coq_Show_ext_fn_t =
    { show0 = (fun h ->
      match h with
      | Coq_ext_mem m ->
        'e'::('x'::('t'::('_'::('m'::('e'::('m'::('_'::(match m with
                                                        | Coq_imem ->
                                                          'i'::('m'::('e'::('m'::[])))
                                                        | Coq_dmem ->
                                                          'd'::('m'::('e'::('m'::[])))))))))))
      | Coq_ext_uart_read ->
        'e'::('x'::('t'::('_'::('u'::('a'::('r'::('t'::('_'::('r'::('e'::('a'::('d'::[]))))))))))))
      | Coq_ext_uart_write ->
        'e'::('x'::('t'::('_'::('u'::('a'::('r'::('t'::('_'::('w'::('r'::('i'::('t'::('e'::[])))))))))))))
      | Coq_ext_led -> 'e'::('x'::('t'::('_'::('l'::('e'::('d'::[]))))))
      | Coq_ext_host_id ->
        'e'::('x'::('t'::('_'::('h'::('o'::('s'::('t'::('_'::('i'::('d'::[]))))))))))
      | Coq_ext_finish ->
        'e'::('x'::('t'::('_'::('f'::('i'::('n'::('i'::('s'::('h'::[])))))))))) }

  (** val rv_ext_fn_sim_specs : ext_fn_t -> ext_fn_sim_spec **)

  let rv_ext_fn_sim_specs fn =
    { efs_name = (coq_Show_ext_fn_t.show0 fn); efs_method =
      (match fn with
       | Coq_ext_finish -> true
       | _ -> false) }

  (** val rv_ext_fn_rtl_specs : ext_fn_t -> ext_fn_rtl_spec **)

  let rv_ext_fn_rtl_specs fn =
    { efr_name = (coq_Show_ext_fn_t.show0 fn); efr_internal =
      (match fn with
       | Coq_ext_host_id -> true
       | Coq_ext_finish -> true
       | _ -> false) }

  (** val coq_FiniteType_rf : Rf.reg_t finiteType **)

  let coq_FiniteType_rf =
    Rf.finite_rf_reg

  (** val coq_FiniteType_scoreboard_rf : Scoreboard.Rf.reg_t finiteType **)

  let coq_FiniteType_scoreboard_rf =
    Scoreboard.finite_rf_reg

  (** val coq_FiniteType_scoreboard : Scoreboard.reg_t finiteType **)

  let coq_FiniteType_scoreboard =
    Scoreboard.finite_reg

  (** val coq_FiniteType_reg_t : reg_t finiteType **)

  let coq_FiniteType_reg_t =
    { finite_index = (fun x ->
      match x with
      | Coq_toIMem state ->
        add 0 (MemReq.coq_FiniteType_reg_t.finite_index state)
      | Coq_fromIMem state ->
        add (Pervasives.succ (Pervasives.succ 0))
          (MemResp.coq_FiniteType_reg_t.finite_index state)
      | Coq_toDMem state ->
        add (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0))))
          (MemReq.coq_FiniteType_reg_t.finite_index state)
      | Coq_fromDMem state ->
        add (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))
          (MemResp.coq_FiniteType_reg_t.finite_index state)
      | Coq_f2d state ->
        add (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0))))))))
          (Coq_fromFetch.coq_FiniteType_reg_t.finite_index state)
      | Coq_f2dprim state ->
        add (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))
          (Coq_waitFromFetch.coq_FiniteType_reg_t.finite_index state)
      | Coq_d2e state ->
        add (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0))))))))))))
          (Coq_fromDecode.coq_FiniteType_reg_t.finite_index state)
      | Coq_e2w state ->
        add (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))
          (Coq_fromExecute.coq_FiniteType_reg_t.finite_index state)
      | Coq_rf state ->
        add (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0))))))))))))))))
          (coq_FiniteType_rf.finite_index state)
      | Coq_stack state ->
        add (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0))))))))))))))))))))))))))))))))))))))))))))))))
          (ShadowStack.coq_FiniteType_reg_t.finite_index state)
      | Coq_scoreboard state ->
        add (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ
          0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          (coq_FiniteType_scoreboard.finite_index state)
      | Coq_cycle_count ->
        Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ
          0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      | Coq_instr_count ->
        Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ
          0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      | Coq_pc ->
        Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ
          0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      | Coq_epoch ->
        Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      | Coq_debug ->
        Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ
          0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      | Coq_on_off ->
        Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ
          0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      | Coq_halt ->
        Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ
          0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
      finite_elements =
      (app
        (map (fun x -> Coq_toIMem x)
          MemReq.coq_FiniteType_reg_t.finite_elements)
        (app
          (map (fun x -> Coq_fromIMem x)
            MemResp.coq_FiniteType_reg_t.finite_elements)
          (app
            (map (fun x -> Coq_toDMem x)
              MemReq.coq_FiniteType_reg_t.finite_elements)
            (app
              (map (fun x -> Coq_fromDMem x)
                MemResp.coq_FiniteType_reg_t.finite_elements)
              (app
                (map (fun x -> Coq_f2d x)
                  Coq_fromFetch.coq_FiniteType_reg_t.finite_elements)
                (app
                  (map (fun x -> Coq_f2dprim x)
                    Coq_waitFromFetch.coq_FiniteType_reg_t.finite_elements)
                  (app
                    (map (fun x -> Coq_d2e x)
                      Coq_fromDecode.coq_FiniteType_reg_t.finite_elements)
                    (app
                      (map (fun x -> Coq_e2w x)
                        Coq_fromExecute.coq_FiniteType_reg_t.finite_elements)
                      (app
                        (map (fun x -> Coq_rf x)
                          coq_FiniteType_rf.finite_elements)
                        (app
                          (map (fun x -> Coq_stack x)
                            ShadowStack.coq_FiniteType_reg_t.finite_elements)
                          (app
                            (map (fun x -> Coq_scoreboard x)
                              coq_FiniteType_scoreboard.finite_elements)
                            (Coq_cycle_count :: (Coq_instr_count :: (Coq_pc :: (Coq_epoch :: (Coq_debug :: (Coq_on_off :: (Coq_halt :: [])))))))))))))))))) }

  (** val coq_FiniteType_reg_t2 : reg_t finiteType **)

  let coq_FiniteType_reg_t2 =
    { finite_index = coq_FiniteType_reg_t.finite_index; finite_elements =
      coq_FiniteType_reg_t.finite_elements }

  type _reg_t = reg_t

  type _ext_fn_t = ext_fn_t

  (** val rv_urules :
      rv_rules_t -> (pos_t, var_t, fn_name_t, reg_t, ext_fn_t) uaction **)

  let rv_urules = function
  | Fetch -> fetch
  | Decode -> decode coq_FiniteType_reg_t2 ShadowStack.coq_FiniteType_reg_t
  | Execute -> execute coq_FiniteType_reg_t2 ShadowStack.coq_FiniteType_reg_t
  | Writeback ->
    writeback coq_FiniteType_reg_t2 ShadowStack.coq_FiniteType_reg_t
  | WaitImem -> wait_imem
  | Imem ->
    mem Coq_imem coq_FiniteType_reg_t2 ShadowStack.coq_FiniteType_reg_t
  | Dmem ->
    mem Coq_dmem coq_FiniteType_reg_t2 ShadowStack.coq_FiniteType_reg_t
  | Tick -> tick
  | UpdateOnOff -> update_on_off
  | EndExecution -> end_execution

  (** val rv_rules :
      rv_rules_t -> (pos_t, var_t, fn_name_t, reg_t, ext_fn_t) rule **)

  let rv_rules = function
  | Fetch ->
    extract_success
      (let desugared = desugar_action dummyPos_unit.dummy_pos fetch in
       tc_action eqDec_string coq_R coq_Sigma dummyPos_unit.dummy_pos []
         (Bits_t 0) desugared)
  | Decode ->
    extract_success
      (let desugared =
         desugar_action dummyPos_unit.dummy_pos
           (decode coq_FiniteType_reg_t2 ShadowStack.coq_FiniteType_reg_t)
       in
       tc_action eqDec_string coq_R coq_Sigma dummyPos_unit.dummy_pos []
         (Bits_t 0) desugared)
  | Execute ->
    extract_success
      (let desugared =
         desugar_action dummyPos_unit.dummy_pos
           (execute coq_FiniteType_reg_t2 ShadowStack.coq_FiniteType_reg_t)
       in
       tc_action eqDec_string coq_R coq_Sigma dummyPos_unit.dummy_pos []
         (Bits_t 0) desugared)
  | Writeback ->
    extract_success
      (let desugared =
         desugar_action dummyPos_unit.dummy_pos
           (writeback coq_FiniteType_reg_t2 ShadowStack.coq_FiniteType_reg_t)
       in
       tc_action eqDec_string coq_R coq_Sigma dummyPos_unit.dummy_pos []
         (Bits_t 0) desugared)
  | WaitImem ->
    extract_success
      (let desugared = desugar_action dummyPos_unit.dummy_pos wait_imem in
       tc_action eqDec_string coq_R coq_Sigma dummyPos_unit.dummy_pos []
         (Bits_t 0) desugared)
  | Imem ->
    extract_success
      (let desugared =
         desugar_action dummyPos_unit.dummy_pos
           (mem Coq_imem coq_FiniteType_reg_t2
             ShadowStack.coq_FiniteType_reg_t)
       in
       tc_action eqDec_string coq_R coq_Sigma dummyPos_unit.dummy_pos []
         (Bits_t 0) desugared)
  | Dmem ->
    extract_success
      (let desugared =
         desugar_action dummyPos_unit.dummy_pos
           (mem Coq_dmem coq_FiniteType_reg_t2
             ShadowStack.coq_FiniteType_reg_t)
       in
       tc_action eqDec_string coq_R coq_Sigma dummyPos_unit.dummy_pos []
         (Bits_t 0) desugared)
  | Tick ->
    extract_success
      (let desugared = desugar_action dummyPos_unit.dummy_pos tick in
       tc_action eqDec_string coq_R coq_Sigma dummyPos_unit.dummy_pos []
         (Bits_t 0) desugared)
  | UpdateOnOff ->
    extract_success
      (let desugared = desugar_action dummyPos_unit.dummy_pos update_on_off in
       tc_action eqDec_string coq_R coq_Sigma dummyPos_unit.dummy_pos []
         (Bits_t 0) desugared)
  | EndExecution ->
    extract_success
      (let desugared = desugar_action dummyPos_unit.dummy_pos end_execution in
       tc_action eqDec_string coq_R coq_Sigma dummyPos_unit.dummy_pos []
         (Bits_t 0) desugared)
 end

module RV32IPackage = Package(RV32I)

(** val prog : unit **)

let prog =
  Backends.register RV32IPackage.package
