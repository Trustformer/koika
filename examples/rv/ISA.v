(*! Definition of the elements required to fully caracterize a RISC-V
    implementation
!*)

(* TODO Privileged ISA *)

Inductive memory_model :=
| RVWMO (* Weak Memory Ordering *).

Inductive base_standard :=
| RV32I (* 32 bits *)
| RV64I (* 64 bits *).
(* in draft: RV32E (32 bits for embedded systems), RV128I (128 bits) *)

Inductive extension :=
| RVM        (* integer multiplication and division *)
| RVA        (* atomic instructions                 *)
| RVF        (* single-precision floating-point     *)
| RVD        (* double-precision floating-point     *)
| RVQ        (* quad-precision floating-point       *)
| RVZiCSR    (* control and status register         *)
| RVZifencei (* instruction-fetch fence             *).
(* in draft: Counters (performance counters and timers),
   L (decimal floating-point), B (bit manipulation),
   J (dynamically translated languages), T (transactional memory),
   P (packed-SIMD), V (vector operations), Zam (misaligned atomics),
   Ztso (total store ordering).
*)

(* Additionally, The RISC-V standard defines the G extension as a shorthand for
   I (base standard) + (M + A + F + D) (extensions).
*)

(* Caracterization of a RISC-V implementation*)
Record ISA := {
  ISA_memory_model  : memory_model  ;
  ISA_base_standard : base_standard ;
  ISA_extensions    : list extension;
}.
