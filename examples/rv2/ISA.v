Require Import MSetInterface MSetWeakList.

(* Standards *)
Inductive memory_model : Type :=
| RVWMO.

Inductive base_standard : Type :=
| RV32I | RV64I.

Inductive extension : Type :=
| RVM | RVA | RVF | RVD | RVQ | RVZiCSR | RVZifencei.

(* Extensions Set *)
Scheme Equality for extension.

Module DecidableExtension <: DecidableType.
  Definition t := extension.
  Definition eq := @eq extension.
  Instance eq_equiv : @Equivalence extension eq := eq_equivalence.
  Definition eq_dec := extension_eq_dec.
End DecidableExtension.

Module ExtensionsSet := MSetWeakList.Make DecidableExtension.

(* ISA *)
Record ISA : Type := {
  ISA_memory_model: memory_model;
  ISA_base_standard : base_standard;
  ISA_activated_extensions : ExtensionsSet.t;
}.
