(*! Implementation of an address stack module !*)
Require Import Koika.Frontend Koika.Std.

Module Type ShadowStackInterface.
  Axiom reg_t            : Type.
  Axiom R                : reg_t -> type.
  Axiom r                : forall idx : reg_t, R idx.
  Axiom push             : UInternalFunction reg_t empty_ext_fn_t.
  Axiom pop              : UInternalFunction reg_t empty_ext_fn_t.
  Axiom FiniteType_reg_t : FiniteType reg_t.
  Axiom Show_reg_t       : Show reg_t.
End ShadowStackInterface.

(* TODO Parameterizing ShadowStackF hurts the instantiation of FiniteType_reg_t *)
(* Module Type ShadowStack_sig. *)
(*   Parameter capacity : nat. *)
(* End ShadowStack_sig. *)

Module ShadowStackF <: ShadowStackInterface.
  Definition capacity := 4.

  (* The + 1 is required for situations where capacity = 2^x *)
  Notation index_sz := (log2 (capacity + 1)).

  (* TODO in general, pow2 (log2 x) != x *)
  Inductive _reg_t := size | stack (n : Vect.index (pow2 index_sz)).
  Definition reg_t := _reg_t.

  Definition R r :=
    match r with
    | size => bits_t index_sz
    | stack n => bits_t 32
    end.

  Definition r reg : R reg :=
    match reg with
    | size => Bits.zero
    | stack n => Bits.zero
    end.

  Definition read_vect_sequential idx : uaction reg_t empty_ext_fn_t :=
    {{ `UCompleteSwitch (SequentialSwitch (bits_t 32) "tmp") index_sz idx
      (fun idx => {{ read0(stack idx) }})` }}.

  Definition write0_stack : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun write0_queue (idx : bits_t index_sz) (val: bits_t 32) : unit_t =>
         `UCompleteSwitch (SequentialSwitchTt) index_sz "idx"
              (fun idx => {{ write0(stack idx, val) }})` }}.

  Definition push : UInternalFunction reg_t empty_ext_fn_t := {{
    fun push (address : bits_t 32) : bits_t 1 =>
      let s0 := read0(size) in
      if (s0 == #(Bits.of_nat index_sz capacity)) then (* overflow *)
        Ob~1
      else (
        write0_stack(s0, address);
        write0(size, s0 + |index_sz`d1|);
        Ob~0
      )
  }}.

  Definition pop : UInternalFunction reg_t empty_ext_fn_t := {{
    fun pop (address : bits_t 32) : bits_t 1 =>
      let s0 := read0(size) in
      let loc := s0 - |index_sz`d1| in
      if s0 == |index_sz`d0| then (* underflow *)
        Ob~1
      else if (`read_vect_sequential "loc"` != address) then (* wrong address *)
        Ob~1
      else (
        write0(size, s0 - |index_sz`d1|);
        Ob~0
      )
  }}.

  Instance Show_reg_t : Show reg_t := _.
  Instance FiniteType_reg_t : FiniteType reg_t := _.
End ShadowStackF.
